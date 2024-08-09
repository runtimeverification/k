from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast import Atts, KAtt
from pyk.kast.inner import KApply, KRewrite, KSequence, KToken, KVariable
from pyk.kast.manip import free_vars
from pyk.kast.outer import KClaim
from pyk.kcfg import KCFG
from pyk.kcfg.semantics import DefaultSemantics
from pyk.prelude.kint import gtInt, intToken, leInt
from pyk.prelude.ml import is_top, mlEqualsTrue
from pyk.proof import APRProof, APRProver, ImpliesProver, ProofStatus, RefutationProof
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import not_none, single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Union

    from pytest import TempPathFactory

    from pyk.kast.inner import KInner
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import KCFGExtendResult
    from pyk.kcfg.semantics import KCFGSemantics
    from pyk.ktool.kprove import KProve

    STATE = Union[tuple[str, str], tuple[str, str, str]]


class RefuteSemantics(DefaultSemantics):
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

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False

    def custom_step(self, c: CTerm) -> KCFGExtendResult | None:
        return None


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
    ) -> tuple[APRProver, APRProof]:
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
        return (APRProver(kcfg_explore), proof)

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

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(proof, max_iterations=1)
        frontier_nodes = proof.pending
        assert proof.status == ProofStatus.PENDING

        assert len(frontier_nodes) == 2
        frontier_node = frontier_nodes[0]
        proof.refute_node(frontier_node)
        proof.unrefute_node(frontier_node)

        prover.advance_proof(proof)

        # Then
        assert proof.status == ProofStatus.PASSED

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

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(proof)

        assert proof.status == ProofStatus.FAILED

        failing_node = single(proof.failing)
        proof.refute_node(failing_node)
        assert len(proof.subproof_ids) == 1

        subproof = single(proof.subproofs)
        assert type(subproof) is RefutationProof
        refutation_prover = ImpliesProver(subproof, kcfg_explore)
        refutation_prover.advance_proof(subproof)

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
        assert proof.status == expected_status

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

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(proof, max_iterations=1)
        frontier_nodes = proof.pending
        assert proof.status == ProofStatus.PENDING

        assert len(frontier_nodes) == 2
        frontier_node = frontier_nodes[0]
        proof.refute_node(frontier_node)

        proof_from_file = APRProof.read_proof_data(proof_dir, proof.id)
        refutation_id = proof.get_refutation_id(frontier_node.id)

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

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(proof)
        failing_node = single(proof.failing)
        predecessors = proof.kcfg.predecessors(failing_node.id)
        assert len(predecessors) == 1
        predecessor_node = predecessors[0].source

        result_predecessor = proof.refute_node(predecessor_node)
        result_successor = proof.refute_node(failing_node)

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

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(proof)
        failing_node = single(proof.failing)
        all_free_vars = {v for c in failing_node.cterm.constraints for v in free_vars(c)}
        assert all_free_vars == {'L', 'M', 'N'}

        refutation = proof.refute_node(failing_node)
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

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)

        # When
        prover.advance_proof(proof)
        failing_node = single(proof.failing)
        refutation = proof.refute_node(failing_node)
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

    def test_apr_proof_refute_node_multiple_constraints(
        self,
        kprove: KProve,
        proof_dir: Path,
        kcfg_explore: KCFGExplore,
    ) -> None:
        # Given
        spec_file = K_FILES / 'refute-node-spec.k'
        spec_module = 'REFUTE-NODE-SPEC'
        claim_id = 'multi-constraint-split'

        prover, proof = self.build_prover(kprove, proof_dir, kcfg_explore, spec_file, spec_module, claim_id)
        cfg = proof.kcfg

        config = cfg.node(1).cterm.config
        l_gt_0 = mlEqualsTrue(gtInt(KVariable('L'), intToken(0)))
        l_le_0 = mlEqualsTrue(leInt(KVariable('L'), intToken(0)))
        m_gt_0 = mlEqualsTrue(gtInt(KVariable('M'), intToken(0)))
        m_le_0 = mlEqualsTrue(leInt(KVariable('M'), intToken(0)))

        cfg.create_node(CTerm(config, [l_gt_0, m_gt_0]))
        cfg.create_node(CTerm(config, [l_gt_0, m_le_0]))
        cfg.create_node(CTerm(config, [l_le_0, m_gt_0]))
        cfg.create_node(CTerm(config, [l_le_0, m_le_0]))

        proof.kcfg.create_split(
            1,
            [
                (
                    3,
                    not_none(cfg.node(1).cterm.match_with_constraint(cfg.node(3).cterm))
                    .add_constraint(l_gt_0)
                    .add_constraint(m_gt_0),
                ),
                (
                    4,
                    not_none(cfg.node(1).cterm.match_with_constraint(cfg.node(4).cterm))
                    .add_constraint(l_gt_0)
                    .add_constraint(m_le_0),
                ),
                (
                    5,
                    not_none(cfg.node(1).cterm.match_with_constraint(cfg.node(5).cterm))
                    .add_constraint(l_le_0)
                    .add_constraint(m_gt_0),
                ),
                (
                    6,
                    not_none(cfg.node(1).cterm.match_with_constraint(cfg.node(6).cterm))
                    .add_constraint(l_le_0)
                    .add_constraint(m_gt_0),
                ),
            ],
        )

        # When
        prover.advance_proof(proof, max_iterations=4)
        # After the minimization, nodes 7-10 created by the advancement of the proof
        # will have multiple constraints in their immediately preceding splits
        proof.kcfg.minimize()

        # Then
        for i in [7, 8, 9, 10]:
            assert proof.refute_node(cfg.node(i)) is not None
