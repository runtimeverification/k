from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence
from pyk.kast.manip import set_cell
from pyk.kcfg.kcfg import Step
from pyk.kcfg.semantics import KCFGSemantics
from pyk.kcfg.show import KCFGShow
from pyk.proof import APRProof, APRProver, ProofStatus
from pyk.proof.show import APRProofNodePrinter
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable
    from typing import Final, Union

    from pytest import TempPathFactory

    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import KCFGExtendResult
    from pyk.ktool.kprove import KProve

    STATE = Union[tuple[str, str], tuple[str, str, str]]

_LOGGER: Final = logging.getLogger(__name__)

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


class CustomStepSemanticsWithoutStep(KCFGSemantics):
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


class TestCustomStep(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'custom-step.k'

    # Disabled until resolved: https://github.com/runtimeverification/haskell-backend/issues/3761
    DISABLE_LEGACY = True

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
        tmp_path_factory: TempPathFactory,
    ) -> None:

        with tmp_path_factory.mktemp('custom_step_tmp_proofs') as proof_dir:
            claim = single(
                kprove.get_claims(
                    Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}']
                )
            )
            kcfg_explore_without_step = create_kcfg_explore(CustomStepSemanticsWithoutStep())
            kcfg_explore_with_step = create_kcfg_explore(CustomStepSemanticsWithStep())

            proof_a = APRProof.from_claim(
                kprove.definition,
                claim,
                subproof_ids=[],
                logs={},
                proof_dir=proof_dir,
            )
            proof_b = APRProof.from_claim(
                kprove.definition,
                claim,
                subproof_ids=[],
                logs={},
                proof_dir=proof_dir,
            )
            init_cterm_a = kcfg_explore_without_step.cterm_symbolic.assume_defined(
                proof_a.kcfg.node(proof_a.init).cterm
            )
            init_cterm_b = kcfg_explore_with_step.cterm_symbolic.assume_defined(proof_b.kcfg.node(proof_b.init).cterm)

            proof_a.kcfg.let_node(proof_a.init, cterm=init_cterm_a)
            proof_b.kcfg.let_node(proof_b.init, cterm=init_cterm_b)

            kcfg_explore_without_step.simplify(proof_a.kcfg, {})
            kcfg_explore_with_step.simplify(proof_b.kcfg, {})

            prover_a = APRProver(
                kcfg_explore=kcfg_explore_without_step,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )
            prover_b = APRProver(
                kcfg_explore=kcfg_explore_with_step,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )

            prover_a.advance_proof(proof_a, max_iterations=max_iterations)
            prover_b.advance_proof(proof_b, max_iterations=max_iterations)

            kcfg_show_a = KCFGShow(
                kprove, node_printer=APRProofNodePrinter(proof_a, kprove, full_printer=True, minimize=False)
            )
            kcfg_show_b = KCFGShow(
                kprove, node_printer=APRProofNodePrinter(proof_b, kprove, full_printer=True, minimize=False)
            )
            cfg_lines_a = kcfg_show_a.show(proof_a.kcfg)
            cfg_lines_b = kcfg_show_b.show(proof_b.kcfg)

            assert cfg_lines_a == cfg_lines_b
            assert proof_a.status == proof_status
