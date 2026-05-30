from __future__ import annotations

import json
from typing import TYPE_CHECKING
from unittest.mock import Mock

import pytest

from pyk.cterm import CSubst
from pyk.cterm.symbolic import CTermImplies
from pyk.kast.prelude.kbool import BOOL
from pyk.kast.prelude.kint import intToken
from pyk.kcfg.exploration import KCFGExplorationNodeAttr
from pyk.kcfg.explore import SimplifyVariant
from pyk.kcfg.kcfg import KCFG, KCFGNodeAttr, KoreHandoff, NodeVariant, NoProgress, Producer, Step
from pyk.proof import EqualityProof
from pyk.proof.implies import EqualitySummary
from pyk.proof.proof import CompositeSummary, Proof, ProofStatus
from pyk.proof.reachability import (
    APRFailureInfo,
    APRProof,
    APRProofAddVariantResult,
    APRProofRecoverAdvanceResult,
    APRProofRecoverCloseResult,
    APRProofRecoverNoProgressResult,
    APRProofStuckResult,
    APRProofTerminalResult,
    APRProver,
    APRSummary,
    DecisiveInvalid,
    Indeterminate,
    LoggedCall,
    RecoverTask,
    Subsumed,
    recover_task_for,
    recovery_rung,
)

from .kcfg.test_minimize import minimization_test_kcfg
from .test_kcfg import node, node_dicts, term

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pytest import TempPathFactory

    from pyk.cterm import CTerm
    from pyk.kcfg.kcfg import NodeAttr
    from pyk.proof.reachability import SubsumptionCheck


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


def apr_proof(i: int, proof_dir: Path, bmc_depth: int | None = None) -> APRProof:
    return APRProof(
        id=f'apr_proof_{i}',
        kcfg=KCFG.from_dict({'nodes': node_dicts(i)}),
        terminal=[],
        init=node(1).id,
        target=node(1).id,
        logs={},
        proof_dir=proof_dir,
        bmc_depth=bmc_depth,
    )


def equality_proof(i: int, proof_dir: Path) -> EqualityProof:
    return EqualityProof(
        id=f'equality_proof_{i}', lhs_body=intToken(i), rhs_body=intToken(i), sort=BOOL, proof_dir=proof_dir
    )


class TestProof:
    def test_read_proof_apr(self, proof_dir: Path) -> None:
        sample_proof = APRProof(
            id='apr_proof_1',
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            terminal=[],
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict

    def test_read_proof_with_attributes(self, proof_dir: Path) -> None:

        kcfg = KCFG.from_dict({'nodes': node_dicts(3)})
        kcfg.add_attr(1, KCFGNodeAttr.VACUOUS)
        kcfg.add_attr(2, KCFGExplorationNodeAttr.TERMINAL)
        sample_proof = APRProof(
            id='apr_proof_1',
            kcfg=kcfg,
            terminal=[],
            init=node(1).id,
            target=node(3).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert type(proof_from_disk) is APRProof
        assert set(sample_proof.kcfg.nodes) == set(proof_from_disk.kcfg.nodes)

    def test_read_proof_aprbmc(self, proof_dir: Path) -> None:
        sample_proof = APRProof(
            id='aprbmc_proof_1',
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            terminal=[],
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
            bmc_depth=1,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict

    def test_read_proof_equality(self, proof_dir: Path) -> None:
        sample_proof = EqualityProof(
            id='equality_proof_1',
            lhs_body=intToken(1),
            rhs_body=intToken(1),
            sort=BOOL,
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict


#### APRProof


def test_read_write_proof_data(proof_dir: Path) -> None:
    kcfg = KCFG(proof_dir / 'apr_proof_1' / 'kcfg')
    node1 = kcfg.create_node(term(1))
    node2 = kcfg.create_node(term(2))
    kcfg.create_node(term(3))
    kcfg.create_node(term(4))

    proof = APRProof(
        id='apr_proof_1',
        kcfg=kcfg,
        terminal=[],
        init=node1.id,
        target=node2.id,
        logs={},
        proof_dir=proof_dir,
    )

    proof.write_proof_data()

    proof_from_disk = APRProof.read_proof_data(id=proof.id, proof_dir=proof_dir)

    assert proof_from_disk.dict == proof.dict


def test_apr_proof_from_dict_no_subproofs(proof_dir: Path) -> None:
    # Given
    proof = apr_proof(1, proof_dir)

    # When
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(id=proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_one_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof_data()
    proof.read_subproof_data(eq_proof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_nested_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    sub_proof_1 = equality_proof(1, proof_dir)
    sub_proof_2 = apr_proof(2, proof_dir)
    sub_proof_3 = apr_proof(3, proof_dir, bmc_depth=3)
    proof = apr_proof(1, proof_dir)

    # When
    sub_proof_1.write_proof_data()
    sub_proof_2.write_proof_data()
    sub_proof_3.write_proof_data()
    proof.read_subproof_data(sub_proof_1.id)
    proof.read_subproof_data(sub_proof_2.id)
    proof.read_subproof_data(sub_proof_3.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_commit_stuck_result_marks_node_stuck() -> None:
    # Given a proof with a pending leaf node that is neither init nor target
    kcfg = KCFG()
    n1 = kcfg.create_node(term(1))
    n2 = kcfg.create_node(term(2))
    n3 = kcfg.create_node(term(3))
    proof = APRProof(id='stuck_proof', kcfg=kcfg, terminal=[], init=n1.id, target=n2.id, logs={})
    assert not kcfg.is_stuck(n3.id)

    # When the coordinator commits a no-progress (stuck) result for that node
    proof.commit(APRProofStuckResult(node_id=n3.id, prior_loops_cache_update=(), optimize_kcfg=False))

    # Then the node is marked stuck — `commit` is the sole `add_stuck` site (C6)
    assert kcfg.is_stuck(n3.id)


_CSUBST_SENTINEL: Final = CSubst()

_CHECK_SUBSUME_DATA: Final = (
    ('subsumed', _CSUBST_SENTINEL, None, Subsumed),
    ('decisive-invalid', None, False, DecisiveInvalid),
    ('decisive-invalid-absent', None, None, DecisiveInvalid),
    ('indeterminate', None, True, Indeterminate),
)


@pytest.mark.parametrize(
    'test_id,csubst,indeterminate,expected',
    _CHECK_SUBSUME_DATA,
    ids=[d[0] for d in _CHECK_SUBSUME_DATA],
)
def test_check_subsume_classification(
    test_id: str,
    csubst: CSubst | None,
    indeterminate: bool | None,
    expected: type[SubsumptionCheck],
) -> None:
    # Given a prover whose implies returns a CTermImplies with the given csubst / indeterminate
    prover = Mock()
    prover.fast_check_subsumption = False
    prover.assume_defined = False
    prover.kcfg_explore.cterm_symbolic.implies.return_value = CTermImplies(csubst, (), None, (), indeterminate)

    # When (call the unbound method with the Mock as self)
    result = APRProver._check_subsume(prover, Mock(id=1), Mock(id=2), proof_id='p')

    # Then the verdict is classified per §1c
    assert isinstance(result, expected)
    if isinstance(result, Subsumed):
        assert result.csubst is csubst


def test_check_subsume_fast_skip_is_decisive_invalid() -> None:
    # Given the fast may-subsume heuristic rejects subsumption
    prover = Mock()
    prover.fast_check_subsumption = True
    prover._may_subsume.return_value = False

    # When
    result = APRProver._check_subsume(prover, Mock(id=1), Mock(id=2), proof_id='p')

    # Then it is a decisive non-subsumption and the backend is never consulted
    assert isinstance(result, DecisiveInvalid)
    prover.kcfg_explore.cterm_symbolic.implies.assert_not_called()


def _node_at_rung(rung: int, attrs: list[NodeAttr]) -> KCFG.Node:
    chain: list[NodeVariant] = []
    if rung >= 1:
        chain = [NodeVariant(Producer.INIT, None, term(1)), NodeVariant(Producer.BOOSTER_SIMPLIFY, 'r-b', term(2))]
    if rung >= 2:
        chain.append(NodeVariant(Producer.KORE_SIMPLIFY, 'r-k', term(3)))
    return KCFG.Node(1, term(rung + 1), attrs, chain)


def test_recovery_rung() -> None:
    assert recovery_rung(KCFG.Node(1, term(1))) == 0
    assert recovery_rung(_node_at_rung(0, [])) == 0
    assert recovery_rung(_node_at_rung(1, [])) == 1
    assert recovery_rung(_node_at_rung(2, [])) == 2


_TASK_DATA: tuple[tuple[str, int, list[NodeAttr], RecoverTask], ...] = (
    # (rung, attrs, expected) — first matching §3d rule
    ('rung0-fresh', 0, [], RecoverTask.TRY_BOOSTER),
    ('rung0-tried', 0, [KCFGNodeAttr.BOOSTER_TRIED], RecoverTask.SIMPLIFY_BOOSTER),
    ('rung1-fresh', 1, [], RecoverTask.TRY_BOOSTER),
    ('rung1-tried', 1, [KCFGNodeAttr.BOOSTER_TRIED], RecoverTask.SIMPLIFY_KORE),
    ('rung2-fresh', 2, [], RecoverTask.TRY_BOOSTER),
    ('rung2-tried', 2, [KCFGNodeAttr.BOOSTER_TRIED], RecoverTask.TRY_KORE),
)


@pytest.mark.parametrize('test_id,rung,attrs,expected', _TASK_DATA, ids=[d[0] for d in _TASK_DATA])
def test_recover_task_selection(test_id: str, rung: int, attrs: list[NodeAttr], expected: RecoverTask) -> None:
    assert recover_task_for(_node_at_rung(rung, attrs)) is expected


def test_recover_task_noop_shortcircuit() -> None:
    # After a no-op SIMPLIFY_BOOSTER, the term advanced to rung 1 but BOOSTER_TRIED stays set
    # (commit's clear-iff-changed invariant), so the next task skips the redundant TRY_BOOSTER and
    # goes straight to SIMPLIFY_KORE.
    node = _node_at_rung(1, [KCFGNodeAttr.BOOSTER_TRIED])
    assert recover_task_for(node) is RecoverTask.SIMPLIFY_KORE


# --- step_proof recover dispatch (C13) -----------------------------------------------------------


def _recover_prover(*, node: KCFG.Node) -> Mock:
    """A Mock APRProver wired enough to exercise the unbound `_recover_*` methods."""
    prover = Mock()
    prover.optimize_kcfg = False
    prover.cut_point_rules = []
    prover.terminal_rules = []
    prover.execute_depth = None
    prover.kcfg_explore.kcfg_semantics.is_terminal.return_value = False
    prover.kcfg_explore.cterm_symbolic.last_request_id = 'req-1'
    prover.kcfg_explore.cterm_symbolic.last_haskell_log_entries = ({'message': 'log'},)
    return prover


def _step(node: KCFG.Node, task: RecoverTask) -> Mock:
    return Mock(node=node, target=node, proof_id='p', circularity=False, nonzero_depth=True, recover_task=task)


def test_recover_simplify_yields_add_variant() -> None:
    node = KCFG.Node(1, term(1))
    prover = _recover_prover(node=node)
    prover.kcfg_explore.simplify_variant.return_value = SimplifyVariant(
        Producer.BOOSTER_SIMPLIFY, term(2), 'req-s', ({'message': 'log'},)
    )

    result = APRProver._recover_simplify(prover, _step(node, RecoverTask.SIMPLIFY_BOOSTER), (), booster_only=True)

    assert len(result) == 1
    variant_result = result[0]
    assert isinstance(variant_result, APRProofAddVariantResult)
    assert variant_result.producer is Producer.BOOSTER_SIMPLIFY
    assert variant_result.cterm == term(2)
    assert variant_result.request_id == 'req-s'


def test_recover_try_booster_close() -> None:
    node = KCFG.Node(1, term(1))
    prover = _recover_prover(node=node)
    prover._check_subsume.return_value = Subsumed(CSubst())

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_BOOSTER), (), is_kore=False)

    assert isinstance(result[-1], APRProofRecoverCloseResult)
    # booster close → no kore handoff
    assert result[-1].kore_request_id is None


def test_recover_try_booster_advance() -> None:
    node = KCFG.Node(1, term(1))
    prover = _recover_prover(node=node)
    prover._check_subsume.return_value = DecisiveInvalid()
    prover.kcfg_explore.extend_cterm.return_value = [Mock()]  # not NoProgress ⇒ advance

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_BOOSTER), (), is_kore=False)

    assert isinstance(result[0], APRProofRecoverAdvanceResult)
    assert result[0].kore_request_id is None


def test_recover_try_booster_no_progress_carries_indeterminate() -> None:
    node = KCFG.Node(1, term(1))
    prover = _recover_prover(node=node)
    prover._check_subsume.return_value = Indeterminate()
    prover.kcfg_explore.extend_cterm.return_value = [NoProgress()]

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_BOOSTER), (), is_kore=False)

    no_progress = result[0]
    assert isinstance(no_progress, APRProofRecoverNoProgressResult)
    assert no_progress.backend == 'booster'
    assert no_progress.subsume_indeterminate is True


def test_recover_try_kore_skips_implies_without_indeterminate_flag() -> None:
    # rung-2 node without SUBSUME_INDETERMINATE: trust the decisive booster invalid, go to execute.
    node = KCFG.Node(1, term(1), [KCFGNodeAttr.BOOSTER_TRIED])
    prover = _recover_prover(node=node)
    prover.kcfg_explore.extend_cterm.return_value = [Mock()]

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_KORE), (), is_kore=True)

    prover._check_subsume.assert_not_called()
    advance = result[0]
    assert isinstance(advance, APRProofRecoverAdvanceResult)
    # kore execute advance → handoff request id captured
    assert advance.kore_request_id == 'req-1'


def test_recover_try_kore_close_records_handoff_id() -> None:
    node = KCFG.Node(1, term(1), [KCFGNodeAttr.SUBSUME_INDETERMINATE])
    prover = _recover_prover(node=node)
    prover._check_subsume.return_value = Subsumed(CSubst())

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_KORE), (), is_kore=True)

    prover._check_subsume.assert_called_once()
    close = result[-1]
    assert isinstance(close, APRProofRecoverCloseResult)
    assert close.kore_request_id == 'req-1'  # kore implies closed ⇒ handoff id set


@pytest.mark.parametrize('subsumption', [Indeterminate(), DecisiveInvalid()], ids=['indeterminate', 'decisive-invalid'])
def test_recover_try_terminal_booster_escalates_instead_of_failing(subsumption: object) -> None:
    # Regression (recover-mode parity): a terminal node whose booster subsumption does not close must
    # NOT be finalized as terminal at the booster rung — that drops it out of `pending` before the
    # ladder can reach a kore implies, regressing proofs that normal mode's kore-capable proxy implies
    # would close.  Both a booster `Indeterminate` and a decisive booster `invalid` escalate: for a
    # terminal node we always want kore's second opinion before declaring it failing.
    node = KCFG.Node(1, term(1))
    prover = _recover_prover(node=node)
    prover.kcfg_explore.kcfg_semantics.is_terminal.return_value = True
    prover._check_subsume.return_value = subsumption

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_BOOSTER), (), is_kore=False)

    # Not finalized as terminal; escalates so the node climbs to TRY_KORE's kore implies.
    assert not any(isinstance(r, APRProofTerminalResult) for r in result)
    no_progress = result[0]
    assert isinstance(no_progress, APRProofRecoverNoProgressResult)
    assert no_progress.backend == 'booster'
    assert no_progress.subsume_indeterminate is True
    prover.kcfg_explore.extend_cterm.assert_not_called()  # a terminal node is never executed


def test_recover_try_terminal_kore_finalizes_when_implies_fails() -> None:
    # The kore rung is the top of the ladder: once the kore implies on a terminal node also fails to
    # close, the node is legitimately finalized as terminal (and so, unsubsumed, becomes failing).
    node = KCFG.Node(1, term(1), [KCFGNodeAttr.SUBSUME_INDETERMINATE])
    prover = _recover_prover(node=node)
    prover.kcfg_explore.kcfg_semantics.is_terminal.return_value = True
    prover._check_subsume.return_value = DecisiveInvalid()

    result = APRProver._recover_try(prover, _step(node, RecoverTask.TRY_KORE), (), is_kore=True)

    prover._check_subsume.assert_called_once()
    assert len(result) == 1
    assert isinstance(result[0], APRProofTerminalResult)
    prover.kcfg_explore.extend_cterm.assert_not_called()


# --- commit recover transitions (C14) ------------------------------------------------------------


def _recover_proof() -> tuple[APRProof, int]:
    kcfg = KCFG()
    n_init = kcfg.create_node(term(1))
    n_target = kcfg.create_node(term(2))
    n = kcfg.create_node(term(3))
    proof = APRProof(id='rec', kcfg=kcfg, terminal=[], init=n_init.id, target=n_target.id, logs={})
    return proof, n.id


def _no_progress(node_id: int, backend: str, indeterminate: bool = False) -> APRProofRecoverNoProgressResult:
    return APRProofRecoverNoProgressResult(
        node_id=node_id,
        prior_loops_cache_update=(),
        optimize_kcfg=False,
        backend=backend,
        subsume_indeterminate=indeterminate,
        logged_calls=(),
    )


def _add_variant(node_id: int, producer: Producer, cterm: CTerm) -> APRProofAddVariantResult:
    return APRProofAddVariantResult(
        node_id=node_id,
        prior_loops_cache_update=(),
        optimize_kcfg=False,
        producer=producer,
        cterm=cterm,
        request_id='r',
        log_entries=None,
    )


def test_commit_no_progress_sets_booster_tried_and_indeterminate() -> None:
    proof, nid = _recover_proof()
    proof.commit(_no_progress(nid, 'booster', indeterminate=True))
    attrs = proof.kcfg.node(nid).attrs
    assert KCFGNodeAttr.BOOSTER_TRIED in attrs
    assert KCFGNodeAttr.SUBSUME_INDETERMINATE in attrs
    assert not proof.kcfg.is_stuck(nid)


def test_commit_add_variant_clear_iff_changed() -> None:
    proof, nid = _recover_proof()
    proof.commit(_no_progress(nid, 'booster', indeterminate=True))

    # No-op simplify (term unchanged): BOOSTER_TRIED stays set → short-circuit to next rung
    proof.commit(_add_variant(nid, Producer.BOOSTER_SIMPLIFY, term(3)))
    assert KCFGNodeAttr.BOOSTER_TRIED in proof.kcfg.node(nid).attrs
    assert recovery_rung(proof.kcfg.node(nid)) == 1

    # A term-changing simplify clears the per-rung try attrs
    proof.commit(_add_variant(nid, Producer.KORE_SIMPLIFY, term(99)))
    cleared = proof.kcfg.node(nid).attrs
    assert KCFGNodeAttr.BOOSTER_TRIED not in cleared
    assert KCFGNodeAttr.SUBSUME_INDETERMINATE not in cleared
    assert recovery_rung(proof.kcfg.node(nid)) == 2


def test_commit_full_ladder_to_both_backends_failed() -> None:
    proof, nid = _recover_proof()
    # rung 0: booster try fails (indeterminate), booster simplify changes the term → rung 1
    proof.commit(_no_progress(nid, 'booster', indeterminate=True))
    proof.commit(_add_variant(nid, Producer.BOOSTER_SIMPLIFY, term(10)))
    # rung 1: booster try fails, kore simplify changes the term → rung 2
    proof.commit(_no_progress(nid, 'booster'))
    proof.commit(_add_variant(nid, Producer.KORE_SIMPLIFY, term(20)))
    # rung 2: booster try fails, then kore try fails → both backends exhausted
    proof.commit(_no_progress(nid, 'booster'))
    assert not proof.kcfg.is_stuck(nid)
    proof.commit(_no_progress(nid, 'kore'))

    node = proof.kcfg.node(nid)
    assert KCFGNodeAttr.BOTH_BACKENDS_FAILED in node.attrs
    assert proof.kcfg.is_stuck(nid)


def test_commit_recover_close_records_implies_handoff() -> None:
    proof, nid = _recover_proof()
    proof.commit(
        APRProofRecoverCloseResult(
            node_id=nid,
            prior_loops_cache_update=(),
            optimize_kcfg=False,
            csubst=CSubst(),
            kore_request_id='r-imp',
            logged_calls=(),
        )
    )
    assert proof.kcfg.kore_handoffs == [
        KoreHandoff(source=nid, target=proof.target, flavour='implies', request_id='r-imp')
    ]


def test_commit_recover_advance_records_execute_handoff() -> None:
    proof, nid = _recover_proof()
    proof.commit(
        APRProofRecoverAdvanceResult(
            node_id=nid,
            prior_loops_cache_update=(),
            optimize_kcfg=False,
            extension_to_apply=Step(term(50), 1, (), []),
            kore_request_id='r-exec',
            logged_calls=(),
        )
    )
    handoffs = proof.kcfg.kore_handoffs
    assert len(handoffs) == 1
    assert handoffs[0].flavour == 'execute'
    assert handoffs[0].source == nid
    assert handoffs[0].request_id == 'r-exec'


def test_commit_recover_advance_no_handoff_for_booster() -> None:
    # A booster advance (kore_request_id None) records no handoff.
    proof, nid = _recover_proof()
    proof.commit(
        APRProofRecoverAdvanceResult(
            node_id=nid,
            prior_loops_cache_update=(),
            optimize_kcfg=False,
            extension_to_apply=Step(term(50), 1, (), []),
            kore_request_id=None,
            logged_calls=(),
        )
    )
    assert proof.kcfg.kore_handoffs == []


def test_commit_writes_recover_logs(proof_dir: Path) -> None:
    kcfg = KCFG()
    n_init = kcfg.create_node(term(1))
    n_target = kcfg.create_node(term(2))
    n = kcfg.create_node(term(3))
    proof = APRProof(id='rec', kcfg=kcfg, terminal=[], init=n_init.id, target=n_target.id, logs={}, proof_dir=proof_dir)
    entries = ({'context': ['proxy'], 'message': 'x'}, {'rule_id': 'abc', 'pre_hash': 'd'})

    proof.commit(
        APRProofRecoverNoProgressResult(
            node_id=n.id,
            prior_loops_cache_update=(),
            optimize_kcfg=False,
            backend='kore',
            subsume_indeterminate=False,
            logged_calls=(LoggedCall('claim-007', entries),),
        )
    )

    assert proof.proof_subdir is not None
    log_file = proof.proof_subdir / 'recover-logs' / 'claim-007.jsonl'
    assert log_file.exists()
    parsed = [json.loads(line) for line in log_file.read_text().splitlines()]
    assert parsed == [dict(entry) for entry in entries]


def test_commit_recover_logs_skipped_when_no_entries(proof_dir: Path) -> None:
    kcfg = KCFG()
    n_init = kcfg.create_node(term(1))
    n_target = kcfg.create_node(term(2))
    n = kcfg.create_node(term(3))
    proof = APRProof(
        id='rec2', kcfg=kcfg, terminal=[], init=n_init.id, target=n_target.id, logs={}, proof_dir=proof_dir
    )

    # A call that captured no entries (None) writes no file.
    proof.commit(
        APRProofRecoverNoProgressResult(
            node_id=n.id,
            prior_loops_cache_update=(),
            optimize_kcfg=False,
            backend='booster',
            subsume_indeterminate=False,
            logged_calls=(LoggedCall('claim-008', None),),
        )
    )

    assert proof.proof_subdir is not None
    assert not (proof.proof_subdir / 'recover-logs' / 'claim-008.jsonl').exists()


def test_apr_proof_minimization_and_terminals() -> None:
    #                                               25   /-- X >=Int 5 --> 10
    #     5    10    15    20   /-- X >=Int 0 --> 6 --> 8
    #  1 --> 2 --> 3 --> 4 --> 5                         \-- X  <Int 5 --> 11
    #              T            \                    30    35     40        T
    #                            \-- X  <Int 0 --> 7 --> 9 --> 12 --> 13
    #                                              T
    proof = APRProof(
        id='apr_min_proof',
        kcfg=minimization_test_kcfg(),
        terminal=[3, 9, 11],
        init=1,
        target=11,
        logs={},
    )

    assert proof.terminal_ids == {3, 9, 11}
    proof.minimize_kcfg()
    assert proof.terminal_ids == {11}


MODULE_NAME_TEST_DATA: Final = (
    ('sq-bracket', 'TEST-KONTROL-TEST-UINT256-BYTES[]-0', 'M-TEST-KONTROL-TEST-UINT256-BYTESbktbkt-0'),
    ('underscore', 'TEST_KONTROL_%)_UINT256-1', 'M-TEST-KONTROL-UINT256-1'),
)


@pytest.mark.parametrize(
    'test_id,proof_id,expected',
    MODULE_NAME_TEST_DATA,
    ids=[test_id for test_id, *_ in MODULE_NAME_TEST_DATA],
)
def test_proof_module_name(test_id: str, proof_id: str, expected: str) -> None:
    # Given
    output = APRProof._make_module_name(proof_id)

    # Then
    assert output == expected


#### APRBMCProof


def test_aprbmc_proof_from_dict_no_subproofs(proof_dir: Path) -> None:
    # Given
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    # When
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(id=proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_one_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    # When
    eq_proof.write_proof_data()
    proof.read_subproof_data(eq_proof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_print_failure_info() -> None:
    failing_nodes = [3, 5]
    pending_nodes = [6, 7, 8]

    path_conditions = {}
    path_conditions[3] = 'true #Equals X <=Int 100'
    path_conditions[5] = '#Top'

    failure_reasons = {}
    failure_reasons[3] = (
        'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\nSTATE_CELL: $n |-> 2 #Implies 1'
    )
    failure_reasons[5] = (
        'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\nSTATE_CELL: $n |-> 5 #Implies 6'
    )

    models: dict[int, list[tuple[str, str]]] = {}
    models[5] = [('X', '101')]

    failure_info = APRFailureInfo(
        failing_nodes=failing_nodes,
        pending_nodes=pending_nodes,
        failure_reasons=failure_reasons,
        path_conditions=path_conditions,
        models=models,
    )

    actual_output = '\n'.join(failure_info.print())
    expected_output = r"""5 Failure nodes. (3 pending and 2 failing)

Pending nodes: [6, 7, 8]

Failing nodes:

  Node id: 3
  Failure reason:
    Structural matching failed, the following cells failed individually (antecedent #Implies consequent):
    STATE_CELL: $n |-> 2 #Implies 1
  Path condition:
    true #Equals X <=Int 100
  Failed to generate a model.

  Node id: 5
  Failure reason:
    Structural matching failed, the following cells failed individually (antecedent #Implies consequent):
    STATE_CELL: $n |-> 5 #Implies 6
  Path condition:
    #Top
  Model:
    X = 101

Join the Runtime Verification Discord server for support: https://discord.gg/CurfmXNtbN"""

    assert actual_output == expected_output


def test_apr_proof_summary(proof_dir: Path) -> None:
    proof = apr_proof(1, proof_dir)

    assert len(proof.summary.summaries) == 1
    assert proof.summary == CompositeSummary(
        [
            APRSummary(
                id='apr_proof_1',
                status=ProofStatus.PASSED,
                admitted=False,
                nodes=1,
                pending=0,
                failing=0,
                vacuous=0,
                stuck=0,
                terminal=0,
                refuted=0,
                bmc_depth=None,
                bounded=0,
                subproofs=0,
                formatted_exec_time='0s',
            )
        ]
    )


def test_aprbmc_proof_summary(proof_dir: Path) -> None:
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    assert len(proof.summary.summaries) == 1
    assert proof.summary == CompositeSummary(
        [
            APRSummary(
                id='apr_proof_1',
                status=ProofStatus.PASSED,
                admitted=False,
                nodes=1,
                pending=0,
                failing=0,
                vacuous=0,
                stuck=0,
                terminal=0,
                refuted=0,
                bmc_depth=1,
                bounded=0,
                subproofs=0,
                formatted_exec_time='0s',
            )
        ]
    )


def test_apr_proof_summary_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    comp_summary = proof_from_disk.summary
    assert isinstance(comp_summary, CompositeSummary)
    assert len(comp_summary.summaries) == 2
    assert comp_summary.summaries[0] == APRSummary(
        id='apr_proof_1',
        status=ProofStatus.PENDING,
        admitted=False,
        nodes=1,
        pending=0,
        failing=0,
        vacuous=0,
        stuck=0,
        terminal=0,
        refuted=0,
        bmc_depth=None,
        bounded=0,
        subproofs=1,
        formatted_exec_time='0s',
    )

    assert comp_summary.summaries[1] == CompositeSummary(
        [
            APRSummary(
                id='apr_proof_2',
                status=ProofStatus.PENDING,
                admitted=False,
                nodes=2,
                pending=1,
                failing=0,
                vacuous=0,
                stuck=0,
                terminal=0,
                refuted=0,
                bmc_depth=None,
                bounded=0,
                subproofs=1,
                formatted_exec_time='0s',
            ),
            EqualitySummary(
                id='equality_proof_1',
                status=ProofStatus.PENDING,
                admitted=False,
            ),
        ]
    )
