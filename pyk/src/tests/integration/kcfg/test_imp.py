from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CSubst, CTerm
from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable, Subst
from pyk.kcfg import KCFG
from pyk.prelude.kbool import BOOL, notBool
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlAnd, mlBottom, mlEqualsFalse, mlEqualsTrue
from pyk.proof import AGBMCProof, AGBMCProver, APRProof, APRProver, EqualityProof, EqualityProver, ProofStatus
from pyk.utils import single

from ..utils import KCFGExploreTest

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.kast.inner import KInner
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprint import KPrint, SymbolTable
    from pyk.ktool.kprove import KProve


PROVE_CTERM_TEST_DATA: Final = (
    ('step-1', ['--depth', '1'], 'int $n , $s ; $n = 3 ;', [('int $s , .Ids ; $n = 3 ;', '$n |-> 0')]),
    ('step-2', ['--depth', '2'], 'int $n , $s ; $n = 3 ;', [('int .Ids ; $n = 3 ;', '$n |-> 0 $s |-> 0')]),
    (
        'branch',
        ['--max-counterexamples', '2', '--depth', '4'],
        'int $n ; if (_B:Bool) { $n = 1; } else { $n = 2; }',
        [('$n = 1 ;', '$n |-> 0'), ('$n = 2 ;', '$n |-> 0')],
    ),
)

EMPTY_STATES: Final[list[tuple[str, str]]] = []
EXECUTE_TEST_DATA: Final = (
    (
        'step-1',
        1,
        ('int $n , $s ; $n = 3 ;', '.Map'),
        1,
        ('int $s , .Ids ; $n = 3 ;', '$n |-> 0'),
        EMPTY_STATES,
    ),
    (
        'step-2',
        2,
        ('int $n , $s ; $n = 3 ;', '.Map'),
        2,
        ('int .Ids ; $n = 3 ;', '$n |-> 0 $s |-> 0'),
        EMPTY_STATES,
    ),
    (
        'branch',
        4,
        ('int $n ; if (_B:Bool) { $n = 1; } else { $n = 2; }', '.Map'),
        2,
        ('if ( _B:Bool ) { $n = 1 ; } else { $n = 2 ; }', '$n |-> 0'),
        [('{ $n = 1 ; }', '$n |-> 0'), ('{ $n = 2 ; }', '$n |-> 0')],
    ),
)


IMPLIES_TEST_DATA: Final = (
    (
        'constant-subst',
        ('int $n , $s ; $n = 3 ;', '.Map'),
        ('int $n , $s ; $n = X ;', '.Map'),
        CSubst(Subst({'X': intToken(3)})),
    ),
    (
        'variable-subst',
        ('int $n , $s ; $n = Y ;', '.Map'),
        ('int $n , $s ; $n = X ;', '.Map'),
        CSubst(Subst({'X': KVariable('Y', sort=KSort('AExp'))})),
    ),
    (
        'trivial',
        ('int $n , $s ; $n = 3 ;', '.Map'),
        ('int $n , $s ; $n = 3 ;', '.Map'),
        CSubst(Subst({})),
    ),
    (
        'consequent-constraint',
        ('int $n , $s ; $n = 3 ;', '.Map'),
        ('int $n , $s ; $n = X ;', '.Map', mlEqualsTrue(KApply('_<Int_', [KVariable('X'), intToken(3)]))),
        None,
    ),
    (
        'antecedent-bottom',
        (
            'int $n , $s ; $n = X ;',
            '.Map',
            mlAnd(
                [
                    mlEqualsTrue(KApply('_<Int_', [KVariable('X'), intToken(3)])),
                    mlEqualsTrue(KApply('_<Int_', [intToken(3), KVariable('X')])),
                ]
            ),
        ),
        ('int $n , $s ; $n = Y ;', '.Map'),
        CSubst(Subst({}), [mlBottom()]),
    ),
)

APR_PROVE_TEST_DATA: Iterable[
    tuple[str, str, str, str, int | None, int | None, Iterable[str], Iterable[str], ProofStatus]
] = (
    (
        'imp-simple-addition-1',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-1',
        2,
        1,
        [],
        [],
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-addition-2',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-2',
        2,
        7,
        [],
        [],
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-addition-var',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-var',
        2,
        1,
        [],
        [],
        ProofStatus.PASSED,
    ),
    (
        'pre-branch-proved',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'pre-branch-proved',
        2,
        100,
        [],
        [],
        ProofStatus.PASSED,
    ),
    (
        'while-cut-rule',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'while-cut-rule',
        2,
        1,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
    ),
    (
        'while-cut-rule-delayed',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'while-cut-rule-delayed',
        4,
        100,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
    ),
    (
        'failing-if',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'failing-if',
        10,
        1,
        [],
        [],
        ProofStatus.FAILED,
    ),
    (
        'imp-simple-sum-10',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-10',
        None,
        None,
        ['IMP-VERIFICATION.halt'],
        [],
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-sum-100',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-100',
        None,
        None,
        ['IMP-VERIFICATION.halt'],
        [],
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-sum-1000',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-1000',
        None,
        None,
        ['IMP-VERIFICATION.halt'],
        [],
        ProofStatus.PASSED,
    ),
)


APRBMC_PROVE_TEST_DATA: Iterable[
    tuple[str, str, str, str, int | None, int | None, int, Iterable[str], Iterable[str], ProofStatus]
] = (
    (
        'bmc-loop-concrete-1',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-concrete',
        20,
        20,
        1,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
    ),
    (
        'bmc-loop-concrete-2',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-concrete',
        20,
        20,
        2,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
    ),
    (
        'bmc-loop-concrete-3',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-concrete',
        20,
        20,
        3,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
    ),
    (
        'bmc-loop-symbolic-1',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-symbolic',
        20,
        20,
        1,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
    ),
    (
        'bmc-loop-symbolic-2',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-symbolic',
        20,
        20,
        2,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
    ),
    (
        'bmc-loop-symbolic-3',
        'k-files/imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-symbolic',
        20,
        20,
        3,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
    ),
)

FUNC_PROVE_TEST_DATA: Iterable[tuple[str, str, str, str, ProofStatus]] = (
    (
        'func-spec-concrete',
        'k-files/imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-addition',
        ProofStatus.PASSED,
    ),
)


class TestImpProof(KCFGExploreTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['.List{"_,_"}_Ids'] = lambda: '.Ids'

    @staticmethod
    def _is_terminal(cterm1: CTerm) -> bool:
        k_cell = cterm1.cell('K_CELL')
        if type(k_cell) is KSequence:
            if len(k_cell) == 0:
                return True
            if len(k_cell) == 1 and type(k_cell[0]) is KVariable:
                return True
        if type(k_cell) is KVariable:
            return True
        return False

    @staticmethod
    def _extract_branches(defn: KDefinition, cterm: CTerm) -> list[KInner]:
        k_cell = cterm.cell('K_CELL')
        if type(k_cell) is KSequence and len(k_cell) > 0:
            k_cell = k_cell[0]
        if type(k_cell) is KApply and k_cell.label.name == 'if(_)_else_':
            condition = k_cell.args[0]
            if (type(condition) is KVariable and condition.sort == BOOL) or (
                type(condition) is KApply and defn.return_sort(condition.label) == BOOL
            ):
                return [mlEqualsTrue(condition), mlEqualsTrue(notBool(condition))]
        return []

    @staticmethod
    def _same_loop(cterm1: CTerm, cterm2: CTerm) -> bool:
        k_cell_1 = cterm1.cell('K_CELL')
        k_cell_2 = cterm2.cell('K_CELL')
        if k_cell_1 == k_cell_2 and type(k_cell_1) is KSequence and type(k_cell_1[0]) is KApply:
            return k_cell_1[0].label.name == 'while(_)_'
        return False

    @staticmethod
    def config(kprint: KPrint, k: str, state: str, constraint: KInner | None = None) -> CTerm:
        k_parsed = kprint.parse_token(KToken(k, 'Pgm'), as_rule=True)
        state_parsed = kprint.parse_token(KToken(state, 'Map'), as_rule=True)
        _config = CTerm(
            KApply(
                '<generatedTop>',
                KApply(
                    '<T>',
                    (
                        KApply('<k>', KSequence(k_parsed)),
                        KApply('<state>', state_parsed),
                    ),
                ),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
            (),
        )
        if constraint is not None:
            _config = _config.add_constraint(constraint)
        return _config

    @pytest.mark.parametrize(
        'test_id,depth,pre,expected_depth,expected_post,expected_next_states',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kcfg_explore: KCFGExplore,
        test_id: str,
        depth: int,
        pre: tuple[str, str],
        expected_depth: int,
        expected_post: tuple[str, str],
        expected_next_states: Iterable[tuple[str, str]],
    ) -> None:
        # Given
        k, state = pre
        expected_k, expected_state = expected_post

        # When
        actual_depth, actual_post_term, actual_next_terms = kcfg_explore.cterm_execute(
            self.config(kcfg_explore.kprint, k, state), depth=depth
        )
        actual_k = kcfg_explore.kprint.pretty_print(actual_post_term.cell('K_CELL'))
        actual_state = kcfg_explore.kprint.pretty_print(actual_post_term.cell('STATE_CELL'))

        actual_next_states = [
            (
                kcfg_explore.kprint.pretty_print(s.cell('K_CELL')),
                kcfg_explore.kprint.pretty_print(s.cell('STATE_CELL')),
            )
            for s in actual_next_terms
        ]

        # Then
        assert actual_k == expected_k
        assert actual_state == expected_state
        assert actual_depth == expected_depth
        assert set(actual_next_states) == set(expected_next_states)

    @pytest.mark.parametrize(
        'test_id,antecedent,consequent,expected',
        IMPLIES_TEST_DATA,
        ids=[test_id for test_id, *_ in IMPLIES_TEST_DATA],
    )
    def test_implies(
        self,
        kcfg_explore: KCFGExplore,
        test_id: str,
        antecedent: tuple[str, str] | tuple[str, str, KInner],
        consequent: tuple[str, str] | tuple[str, str, KInner],
        expected: CSubst | None,
    ) -> None:
        # Given
        antecedent_term = self.config(kcfg_explore.kprint, *antecedent)
        consequent_term = self.config(kcfg_explore.kprint, *consequent)

        # When
        actual = kcfg_explore.cterm_implies(antecedent_term, consequent_term)

        # Then
        assert actual == expected

    def test_assume_defined(
        self,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        k, state = ('PGM', '( $n |-> 0 ) MAP')
        config = self.config(kcfg_explore.kprint, k, state)

        constraint = mlEqualsFalse(
            KApply('_in_keys(_)_MAP_Bool_KItem_Map', KToken('$n', 'Id'), KVariable('MAP', 'Map'))
        )
        expected = config.add_constraint(constraint)

        # When
        actual = kcfg_explore.cterm_assume_defined(config)

        # Then
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,terminal_rules,cut_rules,proof_status',
        APR_PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in APR_PROVE_TEST_DATA],
    )
    def test_all_path_reachability_prove(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        max_iterations: int,
        max_depth: int,
        terminal_rules: Iterable[str],
        cut_rules: Iterable[str],
        proof_status: ProofStatus,
    ) -> None:
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        kcfg = KCFG.from_claim(kprove.definition, claim)
        proof = APRProof(f'{spec_module}.{claim_id}', kcfg)
        prover = APRProver(
            proof,
            is_terminal=TestImpProof._is_terminal,
            extract_branches=lambda cterm: TestImpProof._extract_branches(kprove.definition, cterm),
        )
        kcfg = prover.advance_proof(
            kcfg_explore,
            max_iterations=max_iterations,
            execute_depth=max_depth,
            cut_point_rules=cut_rules,
            terminal_rules=terminal_rules,
        )

        assert proof.status == proof_status

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,bmc_depth,terminal_rules,cut_rules,proof_status',
        APRBMC_PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in APRBMC_PROVE_TEST_DATA],
    )
    def test_all_path_bmc_reachability_prove(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        max_iterations: int,
        max_depth: int,
        bmc_depth: int,
        terminal_rules: Iterable[str],
        cut_rules: Iterable[str],
        proof_status: ProofStatus,
    ) -> None:
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        kcfg = KCFG.from_claim(kprove.definition, claim)
        kcfg_explore.simplify(kcfg)
        proof = AGBMCProof(f'{spec_module}.{claim_id}', kcfg, bmc_depth)
        prover = AGBMCProver(proof, TestImpProof._same_loop, is_terminal=TestImpProof._is_terminal)
        kcfg = prover.advance_proof(
            kcfg_explore,
            max_iterations=max_iterations,
            execute_depth=max_depth,
            cut_point_rules=cut_rules,
            terminal_rules=terminal_rules,
        )

        assert proof.status == proof_status

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,proof_status',
        FUNC_PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in FUNC_PROVE_TEST_DATA],
    )
    def test_functional_prove(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        proof_status: ProofStatus,
    ) -> None:
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        equality_proof = EqualityProof.from_claim(claim, kprove.definition)
        equality_prover = EqualityProver(equality_proof)
        equality_prover.advance_proof(kcfg_explore)

        assert equality_proof.status == proof_status
