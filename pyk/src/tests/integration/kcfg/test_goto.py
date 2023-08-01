from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.kcfg.semantics import KCFGSemantics
from pyk.kcfg.show import KCFGShow
from pyk.prelude.ml import mlEqualsTrue
from pyk.prelude.utils import token
from pyk.proof import APRBMCProof, APRBMCProver, ProofStatus
from pyk.proof.show import APRBMCProofNodePrinter
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.cterm import CTerm
    from pyk.kast.inner import KInner
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprove import KProve
    from pyk.proof import APRProof

_LOGGER: Final = logging.getLogger(__name__)


class GotoSemantics(KCFGSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        return False

    def extract_branches(self, c: CTerm) -> list[KInner]:
        k_cell_pattern = KSequence([KApply('jumpi', [KVariable('JD')])])
        stack_cell_pattern = KApply('ws', [KVariable('S'), KVariable('SS')])
        k_cell_match = k_cell_pattern.match(c.cell('K_CELL'))
        stack_cell_match = stack_cell_pattern.match(c.cell('STACK_CELL'))
        if k_cell_match is not None and stack_cell_match is not None:
            return [
                mlEqualsTrue(KApply('_==Int_', [token(0), stack_cell_match['S']])),
                mlEqualsTrue(KApply('_=/=Int_', [token(0), stack_cell_match['S']])),
            ]
        return []

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        k_cell = c1.cell('K_CELL')
        pc_cell_1 = c1.cell('PC_CELL')
        pc_cell_2 = c2.cell('PC_CELL')
        if pc_cell_1 == pc_cell_2 and type(k_cell) is KSequence and len(k_cell) > 0 and type(k_cell[0]) is KApply:
            return k_cell[0].label.name == 'jumpi'
        return False


APRBMC_PROVE_TEST_DATA: Iterable[
    tuple[str, Path, str, str, int | None, int | None, int, Iterable[str], Iterable[str], ProofStatus, int]
] = (
    (
        'symbolic-loop',
        K_FILES / 'goto.k',
        'GOTO-SPEC',
        'sum-n',
        20,
        20,
        1,
        [],
        [],
        ProofStatus.PASSED,
        3,
    ),
)


def leaf_number(proof: APRProof) -> int:
    non_target_leaves = [nd for nd in proof.kcfg.leaves if not proof.is_target(nd.id)]
    return len(non_target_leaves) + len(proof.kcfg.predecessors(proof.target))


class TestGoToProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'goto.k'

    def semantics(self, definition: KDefinition) -> KCFGSemantics:
        return GotoSemantics()

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
