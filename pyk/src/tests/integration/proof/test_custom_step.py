from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.kast.manip import set_cell
from pyk.kcfg import KCFGExplore
from pyk.kcfg.kcfg import Step
from pyk.kcfg.semantics import DefaultSemantics
from pyk.kcfg.show import KCFGShow
from pyk.proof import APRProof, APRProver, ProofStatus
from pyk.proof.show import APRProofNodePrinter
from pyk.testing import CTermSymbolicTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable
    from typing import Union

    from pyk.cterm import CTermSymbolic
    from pyk.kast.outer import KClaim
    from pyk.kcfg.kcfg import KCFGExtendResult
    from pyk.kcfg.semantics import KCFGSemantics
    from pyk.ktool.kprove import KProve
    from pyk.utils import BugReport

    STATE = Union[tuple[str, str], tuple[str, str, str]]


CUSTOM_STEP_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None, Iterable[str], ProofStatus]] = (
    (
        'a-to-d',
        K_FILES / 'custom-step-spec.k',
        'CUSTOM-STEP-SPEC',
        'a-to-d',
        3,
        4,
        ['CUSTOM-STEP.c.d'],
        ProofStatus.PASSED,
    ),
)


class CustomStepSemanticsWithoutStep(DefaultSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        k_cell = c.cell('K_CELL')
        if (
            type(k_cell) is KSequence
            and type(k_cell[0]) is KApply
            and k_cell[0].label.name == 'd_CUSTOM-STEP-SYNTAX_Step'
        ):
            return True
        return False

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False

    def custom_step(self, c: CTerm) -> KCFGExtendResult | None:
        return None


class CustomStepSemanticsWithStep(CustomStepSemanticsWithoutStep):
    def custom_step(self, c: CTerm) -> KCFGExtendResult | None:
        k_cell = c.cell('K_CELL')
        if (
            type(k_cell) is KSequence
            and type(k_cell[0]) is KApply
            and k_cell[0].label.name == 'c_CUSTOM-STEP-SYNTAX_Step'
        ):
            new_cterm = CTerm.from_kast(set_cell(c.kast, 'K_CELL', KSequence(KApply('d_CUSTOM-STEP-SYNTAX_Step'))))
            return Step(new_cterm, 1, (), ['CUSTOM-STEP.c.d'], cut=True)
        return None


def cterm_template(label: str) -> CTerm:
    return CTerm(
        KApply(
            '<generatedTop>',
            KApply('<k>', KSequence(KApply(label))),
            KApply('<generatedCounter>', KVariable('GENERATEDCOUNTER_CELL', 'Int')),
        ),
    )


CUSTOM_STEP_TEST_DATA_APPLY: Iterable[tuple[str, CTerm, KCFGExtendResult | None]] = (
    (
        'None',
        cterm_template('a_CUSTOM-STEP-SYNTAX_Step'),
        None,
    ),
    (
        'Step',
        cterm_template('c_CUSTOM-STEP-SYNTAX_Step'),
        Step(
            cterm_template('d_CUSTOM-STEP-SYNTAX_Step'),
            1,
            (),
            ['CUSTOM-STEP.c.d'],
            cut=True,
        ),
    ),
)


class TestCustomStep(CTermSymbolicTest, KProveTest):
    KOMPILE_DEFINITION = """
        module CUSTOM-STEP-SYNTAX

            syntax KItem ::= Step
            syntax Step ::= "a" | "b" | "c" | "d"
        endmodule

        module CUSTOM-STEP
            imports CUSTOM-STEP-SYNTAX
            imports K-EQUAL
            configuration <k> $PGM:KItem </k>

            rule [a.b]: <k> a => b ... </k>
            rule [b.c]: <k> b => c ... </k>
            rule [c.d]: <k> c => d ... </k>
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'CUSTOM-STEP'

    @pytest.fixture
    def create_kcfg_explore(
        self,
        cterm_symbolic: CTermSymbolic,
        bug_report: BugReport | None,
    ) -> Callable[[KCFGSemantics], KCFGExplore]:
        def _create_kcfg_explore(kcfg_semantics: KCFGSemantics) -> KCFGExplore:
            return KCFGExplore(cterm_symbolic, kcfg_semantics=kcfg_semantics)

        return _create_kcfg_explore

    @pytest.mark.parametrize(
        'test_id,cterm,expected',
        CUSTOM_STEP_TEST_DATA_APPLY,
        ids=[test_id for test_id, *_ in CUSTOM_STEP_TEST_DATA_APPLY],
    )
    def test_custom_step_exec(self, test_id: str, cterm: CTerm, expected: KCFGExtendResult | None) -> None:

        # When
        kcfg_semantics = CustomStepSemanticsWithStep()
        actual = kcfg_semantics.custom_step(cterm)
        # Then
        assert expected == actual

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,cut_rules,proof_status',
        CUSTOM_STEP_TEST_DATA,
        ids=[test_id for test_id, *_ in CUSTOM_STEP_TEST_DATA],
    )
    def test_cfg_equality(
        self,
        kprove: KProve,
        create_kcfg_explore: Callable[[KCFGSemantics], KCFGExplore],
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        max_iterations: int | None,
        max_depth: int | None,
        cut_rules: Iterable[str],
        proof_status: ProofStatus,
        tmp_path: Path,
    ) -> None:

        proof_dir_a = tmp_path / 'proof_without_custom_step'
        proof_dir_b = tmp_path / 'proof_with_custom_step'
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )
        kcfg_explore_without_step = create_kcfg_explore(CustomStepSemanticsWithoutStep())
        kcfg_explore_with_step = create_kcfg_explore(CustomStepSemanticsWithStep())

        proof_status_a, cfg_proof_a = self._run_proof(
            kcfg_explore_without_step, kprove, claim, cut_rules, proof_dir_a, max_depth, max_iterations
        )
        _, cfg_proof_b = self._run_proof(
            kcfg_explore_with_step, kprove, claim, cut_rules, proof_dir_b, max_depth, max_iterations
        )

        assert proof_status_a == proof_status
        assert cfg_proof_a == cfg_proof_b

    @staticmethod
    def _run_proof(
        kcfg_explore: KCFGExplore,
        kprove: KProve,
        claim: KClaim,
        cut_rules: Iterable[str],
        proof_dir: Path,
        max_depth: int | None,
        max_iterations: int | None,
    ) -> tuple[ProofStatus, list[str]]:

        proof = APRProof.from_claim(kprove.definition, claim, logs={}, proof_dir=proof_dir)
        init_cterm = kcfg_explore.cterm_symbolic.assume_defined(proof.kcfg.node(proof.init).cterm)
        proof.kcfg.let_node(proof.init, cterm=init_cterm)
        kcfg_explore.simplify(proof.kcfg, {})
        prover = APRProver(
            kcfg_explore=kcfg_explore,
            execute_depth=max_depth,
            cut_point_rules=cut_rules,
        )
        prover.advance_proof(proof, max_iterations=max_iterations)

        kcfg_show = KCFGShow(kprove, node_printer=APRProofNodePrinter(proof, kprove, full_printer=True, minimize=False))
        return proof.status, kcfg_show.show(proof.kcfg)
