from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.kcfg import KCFG
from pyk.kcfg.semantics import KCFGSemantics
from pyk.prelude.kint import gtInt, intToken, leInt
from pyk.prelude.ml import mlEqualsTrue
from pyk.proof import APRProof, APRProver, ProofStatus
from pyk.proof.equality import RefutationProof, RefutationProver
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Union

    from pytest import TempPathFactory

    from pyk.cterm import CTerm
    from pyk.kast.inner import KInner
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprove import KProve

    STATE = Union[tuple[str, str], tuple[str, str, str]]


class RefuteSemantics(KCFGSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        k_cell = c.cell('K_CELL')
        if type(k_cell) is KSequence:
            if len(k_cell) == 0:
                return True
            if len(k_cell) == 1 and type(k_cell[0]) is KVariable:
                return True
            if (
                len(k_cell) == 2
                and type(k_cell[1]) is KVariable
                and type(k_cell[0]) is KApply
                and (
                    k_cell[0].label.name == 'e(_)_REFUTE-NODE-SYNTAX_A_Int'
                    or k_cell[0].label.name == 'f(_)_REFUTE-NODE-SYNTAX_A_Int'
                )
            ):
                return True
        if type(k_cell) is KVariable:
            return True
        return False

    def extract_branches(self, c: CTerm) -> list[KInner]:
        k_cell = c.cell('K_CELL')
        if type(k_cell) is KSequence and len(k_cell) > 0:
            k_cell = k_cell[0]
        if type(k_cell) is KApply and k_cell.label.name in [
            'd(_)_REFUTE-NODE-SYNTAX_A_Int',
            'a(_)_REFUTE-NODE-SYNTAX_A_Int',
        ]:
            discriminant = k_cell.args[0]
            return [mlEqualsTrue(gtInt(discriminant, intToken(0))), mlEqualsTrue(leInt(discriminant, intToken(0)))]
        return []

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False


REFUTE_NODE_TEST_DATA: Iterable[tuple[str, Iterable[KInner], ProofStatus]] = (
    ('refute-node-fail', (mlEqualsTrue(leInt(KVariable('N'), intToken(0))),), ProofStatus.FAILED),
)


class TestAPRProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'refute-node.k'

    def semantics(self, definition: KDefinition) -> KCFGSemantics:
        return RefuteSemantics()

    @pytest.fixture(scope='function')
    def proof_dir(self, tmp_path_factory: TempPathFactory) -> Path:
        return tmp_path_factory.mktemp('proofs')

    def test_apr_proof_unrefute_node(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'split-int-succeed'

        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )
        kcfg_pre, init_node, target_node = KCFG.from_claim(kprove.definition, claim, proof_dir)
        proof = APRProof(
            f'{spec_module}.{claim_id}',
            kcfg_pre,
            [],
            init=init_node,
            target=target_node,
            logs={},
            proof_dir=proof_dir,
        )
        prover = APRProver(proof, kcfg_explore)

        # When
        prover.advance_proof(max_iterations=1)
        frontier_nodes = prover.proof.pending
        assert prover.proof.status == ProofStatus.PENDING

        assert len(frontier_nodes)
        frontier_node = frontier_nodes[0]
        prover.refute_node(frontier_node)
        prover.unrefute_node(frontier_node)

        prover.advance_proof()

        # Then
        assert prover.proof.status == ProofStatus.PASSED

    @pytest.mark.parametrize(
        'test_id,expected_subproof_constraints,expected_status',
        REFUTE_NODE_TEST_DATA,
        ids=[test_id for test_id, *_ in REFUTE_NODE_TEST_DATA],
    )
    def test_apr_proof_refute_node(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        proof_dir: Path,
        test_id: str,
        expected_subproof_constraints: Iterable[KInner],
        expected_status: ProofStatus,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'split-int-fail'

        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )
        kcfg_pre, init_node, target_node = KCFG.from_claim(kprove.definition, claim, proof_dir)
        proof = APRProof(
            f'{spec_module}.{claim_id}',
            kcfg_pre,
            [],
            init=init_node,
            target=target_node,
            logs={},
            proof_dir=proof_dir,
        )
        prover = APRProver(
            proof,
            kcfg_explore,
        )

        # When
        prover.advance_proof()

        assert prover.proof.status == ProofStatus.FAILED

        failing_node = single(prover.proof.failing)
        refutation = prover.refute_node(failing_node)
        assert refutation is not None
        refutation_prover = RefutationProver(refutation, kcfg_explore)
        refutation_prover.advance_proof()

        assert len(prover.proof.subproof_ids) == 1
        subproof = single(prover.proof.subproofs)

        assert type(subproof) is RefutationProof

        expected_subproof_constraints = tuple(
            [kprove.definition.sort_vars(constraint) for constraint in expected_subproof_constraints]
        )
        actual_subproof_constraints = tuple(
            [
                kprove.definition.sort_vars(constraint)
                for constraint in (list(subproof.pre_constraints) + [subproof.last_constraint])
            ]
        )

        assert expected_subproof_constraints == actual_subproof_constraints

        # Then
        assert prover.proof.status == expected_status
