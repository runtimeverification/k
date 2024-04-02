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
    from typing import Final

    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import NodeIdLike
    from pyk.ktool.kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)

APR_PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None]] = (
    ('test-nondet', K_FILES / 'non-det-spec.k', 'NON-DET-SPEC', 'non-det', 8, 1),
)


class TestNonDetProof(KCFGExploreTest, KProveTest):
    DISABLE_BOOSTER = True
    KOMPILE_DEFINITION = """
        module NON-DET
            imports INT

            syntax A ::= "a" | "b" | "c" | d(Int) | e(Int) | "f"

            // Raw non-determinism
            rule a => b
            rule a => c

            // Split on new symbolic variable
            rule c => d(?I) ensures ?I >Int 0
            rule c => e(?I) ensures ?I <=Int 0

            // Make it easy to write a claim
            rule b => f
            rule d(_) => f
            rule e(_) => f
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'NON-DET'
    KOMPILE_ARGS = {'syntax_module': 'NON-DET'}

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth',
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
    ) -> None:
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        proof = APRProof.from_claim(kprove.definition, claim, logs={})
        prover = APRProver(proof, kcfg_explore=kcfg_explore, execute_depth=max_depth)
        prover.advance_proof(max_iterations=max_iterations)

        kcfg_show = KCFGShow(kprove, node_printer=APRProofNodePrinter(proof, kprove, full_printer=True))
        cfg_lines = kcfg_show.show(proof.kcfg)
        _LOGGER.info('\n'.join(cfg_lines))

        # We expect this graph, in which all splits are non-deterministic:
        #
        #      id1a - final1 - success
        #     /
        #    /      id1b1 - final2 - success
        # id1      /
        #    \id1b
        #          \
        #           id1b2 - final3 - success

        id1 = proof.init

        def assert_nd_branch(id: NodeIdLike) -> tuple[int, int]:
            assert len(proof.kcfg.successors(source_id=id)) == 1
            ndbranches = proof.kcfg.ndbranches(source_id=id)
            assert len(ndbranches) == 1
            assert len(ndbranches[0].target_ids) == 2
            ida, idb = ndbranches[0].target_ids
            return ida, idb

        def assert_edge(id: int) -> int:
            assert len(proof.kcfg.successors(source_id=id)) == 1
            edges = proof.kcfg.edges(source_id=id)
            assert len(edges) == 1
            return edges[0].target.id

        id1a, id1b = assert_nd_branch(id1)
        if len(proof.kcfg.ndbranches(source_id=id1a)) > len(proof.kcfg.ndbranches(source_id=id1b)):
            (tmp, id1a) = (id1a, id1b)
            id1b = tmp
        id1b1, id1b2 = assert_nd_branch(id1b)

        assert_edge(id1a)
        assert_edge(id1b1)
        assert_edge(id1b2)

        assert proof.status == ProofStatus.PASSED
