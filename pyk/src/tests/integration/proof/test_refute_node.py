from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast import Atts, KAtt
from pyk.kast.inner import KApply, KRewrite, KSequence, KToken, KVariable
from pyk.kast.manip import free_vars
from pyk.kast.outer import KClaim
from pyk.kcfg import KCFG
from pyk.kcfg.semantics import KCFGSemantics
from pyk.prelude.kint import gtInt, intToken, leInt
from pyk.prelude.ml import is_top, mlEqualsTrue
from pyk.proof import APRProof, APRProver, ImpliesProver, ProofStatus, RefutationProof
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
    ('refute-node-fail', (leInt(KVariable('N'), intToken(0)),), ProofStatus.FAILED),
)


class TestAPRProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'refute-node.k'

    def semantics(self, definition: KDefinition) -> KCFGSemantics:
        return RefuteSemantics()

    @pytest.fixture(scope='function')
    def proof_dir(self, tmp_path_factory: TempPathFactory) -> Path:
        return tmp_path_factory.mktemp('proofs')

    def build_prover(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
        spec_file: Path,
        spec_module: str,
        claim_id: str,
    ) -> APRProver:
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
        return APRProver(proof, kcfg_explore)

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

        prover = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(max_iterations=1)
        frontier_nodes = prover.proof.pending
        assert prover.proof.status == ProofStatus.PENDING

        assert len(frontier_nodes) == 2
        frontier_node = frontier_nodes[0]
        prover.proof.refute_node(frontier_node)
        prover.proof.unrefute_node(frontier_node)

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

        prover = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof()

        assert prover.proof.status == ProofStatus.FAILED

        failing_node = single(prover.proof.failing)
        prover.proof.refute_node(failing_node)
        assert len(prover.proof.subproof_ids) == 1

        subproof = single(prover.proof.subproofs)
        assert type(subproof) is RefutationProof
        refutation_prover = ImpliesProver(subproof, kcfg_explore)
        refutation_prover.advance_proof()

        assert subproof.status == ProofStatus.FAILED

        expected_subproof_constraints = tuple(
            [kprove.definition.sort_vars(constraint) for constraint in expected_subproof_constraints]
        )
        actual_subproof_constraints = tuple(
            [
                kprove.definition.sort_vars(constraint)
                for constraint in (list(subproof.pre_constraints) + [subproof.last_constraint])
                if not is_top(constraint)
            ]
        )

        assert expected_subproof_constraints == actual_subproof_constraints

        # Then
        assert prover.proof.status == expected_status

    def test_apr_proof_read_node_refutations(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'split-int-succeed'

        prover = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(max_iterations=1)
        frontier_nodes = prover.proof.pending
        assert prover.proof.status == ProofStatus.PENDING

        assert len(frontier_nodes) == 2
        frontier_node = frontier_nodes[0]
        prover.proof.refute_node(frontier_node)

        proof_from_file = APRProof.read_proof_data(proof_dir, prover.proof.id)
        refutation_id = prover.proof.get_refutation_id(frontier_node.id)

        # Then
        assert len(proof_from_file.node_refutations) == 1
        assert frontier_node.id in proof_from_file.node_refutations
        assert proof_from_file.node_refutations[frontier_node.id].id == refutation_id

    def test_apr_proof_refute_node_no_successors(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'split-int-fail'

        prover = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof()
        failing_node = single(prover.proof.failing)
        predecessors = prover.proof.kcfg.predecessors(failing_node.id)
        assert len(predecessors) == 1
        predecessor_node = predecessors[0].source

        result_predecessor = prover.proof.refute_node(predecessor_node)
        result_successor = prover.proof.refute_node(failing_node)

        # Then
        assert result_predecessor is None  # fails because the node has successors
        assert result_successor is not None  # succeeds because the node has no successors

    def test_apr_proof_refute_node_no_useless_constraints(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'triple-split-int-fail'

        prover = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof()
        failing_node = single(prover.proof.failing)
        all_free_vars = {v for c in failing_node.cterm.constraints for v in free_vars(c)}
        assert all_free_vars == {'L', 'M', 'N'}

        refutation = prover.proof.refute_node(failing_node)
        assert refutation is not None

        # Then

        # last_constraint = (N <=Int 0)
        # pre_constraints = [(L +Int N <=Int 0)]
        # (M <=Int 0) has been removed from pre_constraints because it is independent from last_constraint
        assert len(refutation.pre_constraints) == 1
        refutation_free_vars = set(free_vars(refutation.pre_constraints[0]))
        assert refutation_free_vars == {'L', 'N'}

    def test_apr_proof_refute_node_to_claim(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'triple-split-int-fail'

        prover = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof()
        failing_node = single(prover.proof.failing)
        refutation = prover.proof.refute_node(failing_node)
        assert refutation is not None

        claim, _ = refutation.to_claim('refute-node-claim')

        # Then

        # claim ['refute-node-claim']: <k> ( N:Int <=Int 0 => false ) </k>
        #   requires _L +Int N:Int <=Int 0 [label(refute-node-claim)]
        expected = KClaim(
            body=KRewrite(KApply('_<=Int_', KVariable('N', 'Int'), KToken('0', 'Int')), KToken('false', 'Bool')),
            requires=KApply(
                '_<=Int_', KApply('_+Int_', KVariable('_L', None), KVariable('N', 'Int')), KToken('0', 'Int')
            ),
            att=KAtt(entries=[Atts.LABEL('refute-node-claim')]),
        )

        assert claim == expected
