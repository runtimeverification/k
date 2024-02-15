from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

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

    from pyk.kcfg import KCFGExplore
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


def leaf_number(proof: APRProof) -> int:
    non_target_leaves = [nd for nd in proof.kcfg.leaves if not proof.is_target(nd.id)]
    return len(non_target_leaves) + len(proof.kcfg.predecessors(proof.target))


class TestMiniKEVM(KCFGExploreTest, KProveTest):
    DISABLE_BOOSTER = True
    KOMPILE_MAIN_FILE = K_FILES / 'mini-kevm.k'

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

            new_init_cterm = kcfg_explore.cterm_assume_defined(proof.kcfg.node(proof.init).cterm)
            proof.kcfg.replace_node(proof.init, new_init_cterm)
            kcfg_explore.simplify(proof.kcfg, {})

            prover = APRProver(
                proof,
                kcfg_explore=kcfg_explore,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )
            prover.advance_proof(max_iterations=max_iterations)

            kcfg_show = KCFGShow(
                kcfg_explore.kprint,
                node_printer=APRProofNodePrinter(proof, kcfg_explore.kprint, full_printer=True, minimize=False),
            )
            cfg_lines = kcfg_show.show(proof.kcfg)
            _LOGGER.info('\n'.join(cfg_lines))

            assert proof.status == proof_status
            assert leaf_number(proof) == expected_leaf_number
