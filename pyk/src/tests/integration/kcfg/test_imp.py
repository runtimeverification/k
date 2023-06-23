from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CSubst, CTerm
from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable, Subst
from pyk.kast.manip import minimize_term
from pyk.kcfg.show import KCFGShow
from pyk.prelude.kbool import BOOL, notBool
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlAnd, mlBottom, mlEqualsFalse, mlEqualsTrue
from pyk.proof import APRBMCProof, APRBMCProver, APRProof, APRProver, ProofStatus
from pyk.proof.show import APRBMCProofNodePrinter, APRProofNodePrinter
from pyk.testing import KCFGExploreTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pytest import TempPathFactory

    from pyk.kast.inner import KInner
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprint import KPrint, SymbolTable
    from pyk.ktool.kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)


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

IMPLICATION_FAILURE_TEST_DATA: Final = (
    (
        'different-cell',
        ('int $n ; $n = 0 ;', '.Map'),
        ('int $n ; $n = 1 ;', '.Map'),
        (
            'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\n'
            'K_CELL: int $n , .Ids ; $n = 0 ; #Implies int $n , .Ids ; $n = 1 ;'
        ),
    ),
    (
        'different-cell-2',
        ('int $n ; $n = X:Int ;', '.Map'),
        ('int $n ; $n = 1 ;', '.Map'),
        (
            'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\n'
            'K_CELL: int $n , .Ids ; $n = X:Int ; #Implies int $n , .Ids ; $n = 1 ;'
        ),
    ),
    (
        'different-constraint',
        (
            'int $n ; $n = 0 ;',
            '1 |-> A:Int 2 |-> B:Int',
            mlAnd(
                [
                    mlEqualsTrue(KApply('_<Int_', [KVariable('A', 'Int'), KToken('1', 'Int')])),
                    mlEqualsTrue(KApply('_<Int_', [KVariable('B', 'Int'), KToken('1', 'Int')])),
                ]
            ),
        ),
        (
            'int $n ; $n = 0 ;',
            '1 |-> A:Int 2 |-> B:Int',
            mlAnd(
                [
                    mlEqualsTrue(KApply('_<Int_', [KVariable('A', 'Int'), KToken('1', 'Int')])),
                    mlEqualsTrue(KApply('_<Int_', [KVariable('B', 'Int'), KToken('2', 'Int')])),
                ]
            ),
        ),
        (
            'Implication check failed, the following is the remaining implication:\n'
            '{ true #Equals A:Int <Int 1 }\n'
            '#And { true #Equals B:Int <Int 1 } #Implies { true #Equals B:Int <Int 2 }'
        ),
    ),
    (
        'different-constraint-with-match',
        (
            'int $n ; $n = 0 ;',
            '1 |-> A:Int 2 |-> B:Int',
            mlAnd(
                [
                    mlEqualsTrue(KApply('_<Int_', [KVariable('A', 'Int'), KToken('1', 'Int')])),
                    mlEqualsTrue(KApply('_<Int_', [KVariable('B', 'Int'), KToken('1', 'Int')])),
                ]
            ),
        ),
        (
            'int $n ; $n = X:Int ;',
            '1 |-> A:Int 2 |-> B:Int',
            mlAnd(
                [
                    mlEqualsTrue(KApply('_<Int_', [KVariable('A', 'Int'), KToken('1', 'Int')])),
                    mlEqualsTrue(KApply('_<Int_', [KVariable('B', 'Int'), KToken('2', 'Int')])),
                ]
            ),
        ),
        (
            'Implication check failed, the following is the remaining implication:\n'
            '{ true #Equals A:Int <Int 1 }\n'
            '#And { true #Equals B:Int <Int 1 } #Implies { true #Equals B:Int <Int 2 }'
        ),
    ),
    (
        'substitution',
        ('int $n ; $n = 5 ;', '3 |-> 6'),
        ('int $n ; $n = X:Int ;', '3 |-> X:Int'),
        (
            'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\n'
            'STATE_CELL: 3 |-> 6 #Implies X:Int'
        ),
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

APR_PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None, Iterable[str], ProofStatus, int]] = (
    (
        'imp-simple-addition-1',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-1',
        2,
        1,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'imp-simple-addition-2',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-2',
        2,
        7,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'imp-simple-addition-var',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-var',
        2,
        1,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'pre-branch-proved',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'pre-branch-proved',
        2,
        100,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'while-cut-rule',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'while-cut-rule',
        2,
        1,
        ['IMP.while'],
        ProofStatus.PASSED,
        1,
    ),
    (
        'while-cut-rule-delayed',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'while-cut-rule-delayed',
        4,
        100,
        ['IMP.while'],
        ProofStatus.PASSED,
        1,
    ),
    (
        'failing-if',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'failing-if',
        10,
        1,
        [],
        ProofStatus.FAILED,
        2,
    ),
    (
        'imp-simple-sum-10',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-10',
        None,
        None,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'imp-simple-sum-100',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-100',
        None,
        None,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'imp-simple-sum-1000',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-1000',
        None,
        None,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'imp-if-almost-same-plus',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC-DEPENDENCIES',
        'if-almost-same-plus',
        None,
        None,
        [],
        ProofStatus.PASSED,
        2,
    ),
    (
        'imp-if-almost-same-times',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'if-almost-same-times',
        None,
        None,
        [],
        ProofStatus.PASSED,
        2,
    ),
    (
        'imp-use-if-almost-same',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'use-if-almost-same',
        None,
        None,
        [],
        ProofStatus.PASSED,
        1,  # We can reuse subproofs.
    ),
    (
        'imp-use-if-almost-same-twice',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'use-if-almost-same-twice',
        None,
        None,
        [],
        ProofStatus.PASSED,
        1,  # We can reuse subproofs.
    ),
    (
        'imp-simple-sum-loop',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-loop',
        None,
        None,
        ['IMP.while'],  # If we do not include `IMP.while` in this list, we get 4 branches instead of 2
        ProofStatus.PASSED,
        2,
    ),
    (
        'imp-simple-sum-N',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-N',
        None,
        None,
        [],
        ProofStatus.PASSED,
        1,
    ),
    (
        'imp-failing-circularity',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'failing-circularity',
        None,
        None,
        [],
        ProofStatus.FAILED,
        1,
    ),
)

PATH_CONSTRAINTS_TEST_DATA: Iterable[
    tuple[str, Path, str, str, int | None, int | None, Iterable[str], Iterable[str], str]
] = (
    (
        'imp-simple-fail-branch',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'fail-branch',
        None,
        1,
        [],
        [],
        '{ true #Equals notBool _S:Int <=Int 123 }',
    ),
)


APRBMC_PROVE_TEST_DATA: Iterable[
    tuple[str, Path, str, str, int | None, int | None, int, Iterable[str], Iterable[str], ProofStatus, int]
] = (
    (
        'bmc-loop-concrete-1',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-concrete',
        20,
        20,
        0,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
        1,
    ),
    (
        'bmc-loop-concrete-2',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-concrete',
        20,
        20,
        1,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
        1,
    ),
    (
        'bmc-loop-concrete-3',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-concrete',
        20,
        20,
        2,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
        1,
    ),
    (
        'bmc-loop-symbolic-1',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-symbolic',
        20,
        20,
        0,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
        2,
    ),
    (
        'bmc-loop-symbolic-2',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-symbolic',
        20,
        20,
        1,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
        3,
    ),
    (
        'bmc-loop-symbolic-3',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-loop-symbolic',
        20,
        20,
        2,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
        3,
    ),
    (
        'bmc-two-loops-symbolic-1',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-two-loops-symbolic',
        20,
        20,
        0,
        [],
        ['IMP.while'],
        ProofStatus.PASSED,
        3,
    ),
    (
        'bmc-two-loops-symbolic-2',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'bmc-two-loops-symbolic',
        50,
        20,
        1,
        [],
        ['IMP.while'],
        ProofStatus.FAILED,
        7,
    ),
)


def leaf_number(proof: APRProof) -> int:
    non_target_leaves = [nd for nd in proof.kcfg.leaves if not proof.is_target(nd.id)]
    return len(non_target_leaves) + len(proof.kcfg.predecessors(proof.target))


class TestImpProof(KCFGExploreTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp-verification.k'

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
        actual_depth, actual_post_term, actual_next_terms, _logs = kcfg_explore.cterm_execute(
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
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,cut_rules,proof_status,expected_leaf_number',
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
        max_iterations: int | None,
        max_depth: int | None,
        cut_rules: Iterable[str],
        proof_status: ProofStatus,
        expected_leaf_number: int,
        tmp_path_factory: TempPathFactory,
    ) -> None:
        with tmp_path_factory.mktemp('apr_tmp_proofs') as proof_dir:
            claim = single(
                kprove.get_claims(
                    Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}']
                )
            )

            deps = claim.dependencies

            def qualify(module: str, label: str) -> str:
                if '.' in label:
                    return label
                return f'{module}.{label}'

            subproof_ids = [qualify(spec_module, dep_id) for dep_id in deps]

            # < Admit all the dependencies >
            # We create files for all the subproofs, all tagged as `admitted`.
            # Later, when creating the proof for the main claim, these get loaded
            # and their status will be `PASSED`. This is similar to how Coq handles admitted lemmas.
            # We do all this in order to decouple the tests of "main theorems" from tests of its dependencies.
            deps_claims = kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=subproof_ids)

            deps_proofs = [
                APRProof.from_claim(kprove.definition, c, subproof_ids=[], logs={}, proof_dir=proof_dir)
                for c in deps_claims
            ]
            for dp in deps_proofs:
                dp.admit()
                dp.write_proof()
            # </Admit all the dependencies >

            proof = APRProof.from_claim(
                kprove.definition,
                claim,
                subproof_ids=subproof_ids,
                circularity=claim.is_circularity,
                logs={},
                proof_dir=proof_dir,
            )
            _msg_suffix = ' (and is a circularity)' if claim.is_circularity else ''
            _LOGGER.info(f"The claim '{spec_module}.{claim_id}' has {len(subproof_ids)} dependencies{_msg_suffix}")

            prover = APRProver(
                proof,
                kcfg_explore=kcfg_explore,
                is_terminal=TestImpProof._is_terminal,
                extract_branches=lambda cterm: TestImpProof._extract_branches(kprove.definition, cterm),
            )

            prover.advance_proof(
                max_iterations=max_iterations,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )

            kcfg_show = KCFGShow(
                kcfg_explore.kprint, node_printer=APRProofNodePrinter(proof, kcfg_explore.kprint, full_printer=True)
            )
            cfg_lines = kcfg_show.show(proof.kcfg)
            _LOGGER.info('\n'.join(cfg_lines))

            assert proof.status == proof_status
            assert leaf_number(proof) == expected_leaf_number

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,terminal_rules,cut_rules,expected_constraint',
        PATH_CONSTRAINTS_TEST_DATA,
        ids=[test_id for test_id, *_ in PATH_CONSTRAINTS_TEST_DATA],
    )
    def test_collect_path_constraints(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        max_iterations: int | None,
        max_depth: int | None,
        terminal_rules: Iterable[str],
        cut_rules: Iterable[str],
        expected_constraint: str,
    ) -> None:
        def _node_printer(cterm: CTerm) -> list[str]:
            _kast = minimize_term(cterm.kast)
            return kcfg_explore.kprint.pretty_print(_kast).split('\n')

        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        proof = APRProof.from_claim(kprove.definition, claim, logs={})
        prover = APRProver(
            proof,
            kcfg_explore=kcfg_explore,
            is_terminal=TestImpProof._is_terminal,
            extract_branches=lambda cterm: TestImpProof._extract_branches(kprove.definition, cterm),
        )

        prover.advance_proof(
            max_iterations=max_iterations,
            execute_depth=max_depth,
            cut_point_rules=cut_rules,
            terminal_rules=terminal_rules,
        )

        assert len(proof.terminal) == 1
        path_constraint = proof.path_constraints(proof.terminal[0].id)
        actual_constraint = kcfg_explore.kprint.pretty_print(path_constraint).replace('\n', ' ')
        assert actual_constraint == expected_constraint

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,bmc_depth,terminal_rules,cut_rules,proof_status,expected_leaf_number',
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
        max_iterations: int | None,
        max_depth: int | None,
        bmc_depth: int,
        terminal_rules: Iterable[str],
        cut_rules: Iterable[str],
        proof_status: ProofStatus,
        expected_leaf_number: int,
    ) -> None:
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        proof = APRBMCProof.from_claim_with_bmc_depth(kprove.definition, claim, bmc_depth)
        kcfg_explore.simplify(proof.kcfg, {})
        prover = APRBMCProver(
            proof,
            kcfg_explore=kcfg_explore,
            same_loop=TestImpProof._same_loop,
            is_terminal=TestImpProof._is_terminal,
        )
        prover.advance_proof(
            max_iterations=max_iterations,
            execute_depth=max_depth,
            cut_point_rules=cut_rules,
            terminal_rules=terminal_rules,
        )

        kcfg_show = KCFGShow(
            kcfg_explore.kprint, node_printer=APRBMCProofNodePrinter(proof, kcfg_explore.kprint, full_printer=True)
        )
        cfg_lines = kcfg_show.show(proof.kcfg)
        _LOGGER.info('\n'.join(cfg_lines))

        assert proof.status == proof_status
        assert leaf_number(proof) == expected_leaf_number
