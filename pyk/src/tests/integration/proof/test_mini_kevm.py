from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KVariable
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
    from collections.abc import Iterable
    from typing import Final, Union

    from pytest import TempPathFactory

    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import KCFGExtendResult
    from pyk.ktool.kprove import KProve

    STATE = Union[tuple[str, str], tuple[str, str, str]]

_LOGGER: Final = logging.getLogger(__name__)


APR_PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None, Iterable[str], ProofStatus, int]] = (
    (
        'ensures-constraint-simplification',
        K_FILES / 'mini-kevm-spec.k',
        'MINI-KEVM-SPEC',
        'ensures-constraint',
        2,
        1,
        [],
        ProofStatus.PASSED,
        1,
    ),
)


CUSTOM_STEP_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None, Iterable[str], ProofStatus, int]] = (
    (
        'check-custom-step',
        K_FILES / 'mini-kevm-spec.k',
        'MINI-KEVM-SPEC',
        'custom-step',
        2,
        1,
        ['MINI-KEVM.setId'],
        ProofStatus.PASSED,
        1,
    ),
)

skip_custom_step = False


def leaf_number(proof: APRProof) -> int:
    non_target_leaves = [nd for nd in proof.kcfg.leaves if not proof.is_target(nd.id)]
    return len(non_target_leaves) + len(proof.kcfg.predecessors(proof.target))


class MiniKEVMSemantics(KCFGSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        k_cell = c.cell('K_CELL')
        if (
            type(k_cell) is KSequence
            and type(k_cell[0]) is KApply
            and k_cell[0].label.name == 'b_MINI-KEVM-SYNTAX_KItem'
        ):
            return True
        return False

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False

    def custom_step(self, c: CTerm) -> KCFGExtendResult | None:
        global skip_custom_step

        pattern = KSequence(
            [KApply('setId__MINI-KEVM-SYNTAX_KItem_Int', KVariable('###X')), KVariable('###CONTINUATION')]
        )
        subst = pattern.match(c.cell('K_CELL'))
        if subst is None or skip_custom_step:
            return None
        new_cterm = CTerm.from_kast(
            set_cell(c.kast, 'ID_CELL', KApply('chop(_)_MINI-KEVM-SYNTAX_Int_Int', [subst['###X']]))
        )
        new_cterm = CTerm.from_kast(
            set_cell(new_cterm.kast, 'K_CELL', KSequence(KApply('b_MINI-KEVM-SYNTAX_KItem'), subst['###CONTINUATION']))
        )
        return Step(new_cterm, 1, (), ['MINI-KEVM.setId'], cut=True)


class TestMiniKEVM(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'mini-kevm.k'
    # Disabled until resolved: https://github.com/runtimeverification/haskell-backend/issues/3761
    DISABLE_LEGACY = True

    def semantics(self, definition: KDefinition) -> KCFGSemantics:
        return MiniKEVMSemantics()

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
            proof = APRProof.from_claim(
                kprove.definition,
                claim,
                subproof_ids=[],
                logs={},
                proof_dir=proof_dir,
            )

            new_init_cterm = kcfg_explore.cterm_symbolic.assume_defined(proof.kcfg.node(proof.init).cterm)
            proof.kcfg.let_node(proof.init, cterm=new_init_cterm)
            kcfg_explore.simplify(proof.kcfg, {})

            prover = APRProver(
                kcfg_explore=kcfg_explore,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )
            prover.advance_proof(proof, max_iterations=max_iterations)

            kcfg_show = KCFGShow(
                kprove, node_printer=APRProofNodePrinter(proof, kprove, full_printer=True, minimize=False)
            )
            cfg_lines = kcfg_show.show(proof.kcfg)
            _LOGGER.info('\n'.join(cfg_lines))

            assert proof.status == proof_status
            assert leaf_number(proof) == expected_leaf_number

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,cut_rules,proof_status,expected_leaf_number',
        CUSTOM_STEP_TEST_DATA,
        ids=[test_id for test_id, *_ in CUSTOM_STEP_TEST_DATA],
    )
    def test_custom_step(
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
        global skip_custom_step

        skip_custom_step = False

        with tmp_path_factory.mktemp('custom_step_tmp_proofs') as proof_dir:
            claim = single(
                kprove.get_claims(
                    Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}']
                )
            )
            proof1 = APRProof.from_claim(
                kprove.definition,
                claim,
                subproof_ids=[],
                logs={},
                proof_dir=proof_dir,
            )

            proof2 = APRProof.from_claim(
                kprove.definition,
                claim,
                subproof_ids=[],
                logs={},
                proof_dir=proof_dir,
            )
            new_init_cterm1 = kcfg_explore.cterm_symbolic.assume_defined(proof1.kcfg.node(proof1.init).cterm)
            proof1.kcfg.let_node(proof1.init, cterm=new_init_cterm1)
            kcfg_explore.simplify(proof1.kcfg, {})

            prover1 = APRProver(
                kcfg_explore=kcfg_explore,
                execute_depth=max_depth,
                cut_point_rules=[],
            )
            prover1.advance_proof(proof1, max_iterations=max_iterations)

            new_init_cterm2 = kcfg_explore.cterm_symbolic.assume_defined(proof1.kcfg.node(proof1.init).cterm)
            proof2.kcfg.let_node(proof2.init, cterm=new_init_cterm2)
            kcfg_explore.simplify(proof2.kcfg, {})

            skip_custom_step = True

            prover2 = APRProver(
                kcfg_explore=kcfg_explore,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )
            prover2.advance_proof(proof2, max_iterations=max_iterations)

            kcfg_show = KCFGShow(
                kprove, node_printer=APRProofNodePrinter(proof2, kprove, full_printer=True, minimize=False)
            )
            cfg_lines1 = kcfg_show.show(proof1.kcfg)
            _LOGGER.info('\n'.join(cfg_lines1))

            cfg_lines2 = kcfg_show.show(proof2.kcfg)
            _LOGGER.info('\n'.join(cfg_lines2))

            assert cfg_lines1 == cfg_lines2
            assert proof1.status == proof_status
            assert proof2.status == proof_status
            assert leaf_number(proof1) == expected_leaf_number
            assert leaf_number(proof2) == expected_leaf_number
