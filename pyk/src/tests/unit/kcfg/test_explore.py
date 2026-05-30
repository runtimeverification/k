from __future__ import annotations

from unittest.mock import Mock

import pytest

from pyk.cterm.symbolic import CTermExecute
from pyk.kcfg.explore import KCFGExplore
from pyk.kcfg.kcfg import NoProgress, Producer, Step

from ..test_kcfg import term


def _explore(exec_result: CTermExecute) -> KCFGExplore:
    cterm_symbolic = Mock()
    cterm_symbolic.execute.return_value = exec_result
    # DefaultSemantics: custom_step → None, abstract_node → identity, so extend_cterm reaches execute.
    return KCFGExplore(cterm_symbolic)


def test_extend_cterm_reports_no_progress_not_stuck() -> None:
    # Given a backend that makes no progress (depth 0, no next states, not vacuous)
    cterm = term(1)
    explore = _explore(CTermExecute(state=cterm, next_states=(), depth=0, vacuous=False, aborted=False, logs=()))

    # When
    results = explore.extend_cterm(cterm, node_id=1)

    # Then the worker emits the neutral NoProgress signal — never Stuck (the coordinator decides)
    assert len(results) == 1
    assert isinstance(results[0], NoProgress)


def test_extend_cterm_step_on_progress() -> None:
    # Given a backend that makes progress
    cterm = term(1)
    nxt = term(2)
    explore = _explore(CTermExecute(state=nxt, next_states=(), depth=3, vacuous=False, aborted=False, logs=()))

    # When
    results = explore.extend_cterm(cterm, node_id=1)

    # Then a basic-block Step is produced (unchanged behaviour)
    assert len(results) == 1
    assert isinstance(results[0], Step)


@pytest.mark.parametrize(
    'booster_only,expected_producer',
    [(True, Producer.BOOSTER_SIMPLIFY), (False, Producer.KORE_SIMPLIFY)],
    ids=['booster', 'kore'],
)
def test_simplify_variant_producer_and_capture(booster_only: bool, expected_producer: Producer) -> None:
    # Given a cterm_symbolic that simplifies to a new term and exposes request id + log entries
    entries = ({'context': ['proxy'], 'message': 'x'},)
    cterm_symbolic = Mock()
    cterm_symbolic.simplify.return_value = (term(2), ())
    cterm_symbolic.last_request_id = 'claim-001'
    cterm_symbolic.last_haskell_log_entries = entries
    explore = KCFGExplore(cterm_symbolic)

    # When
    variant = explore.simplify_variant(term(1), booster_only=booster_only)

    # Then the producer matches the backend, and request_id + entries are captured
    assert variant.producer is expected_producer
    assert variant.cterm == term(2)
    assert variant.request_id == 'claim-001'
    assert variant.log_entries == entries
    # And the simplify was invoked with logging on and the right backend
    _args, kwargs = cterm_symbolic.simplify.call_args
    assert kwargs['booster_only_simplify'] is booster_only
    assert kwargs['haskell_logging'] is True


def test_simplify_variant_noop_still_yields_variant() -> None:
    # Given a no-op simplification (term unchanged)
    cterm_symbolic = Mock()
    cterm_symbolic.simplify.return_value = (term(1), ())
    cterm_symbolic.last_request_id = 'claim-002'
    cterm_symbolic.last_haskell_log_entries = None
    explore = KCFGExplore(cterm_symbolic)

    # When
    variant = explore.simplify_variant(term(1), booster_only=True)

    # Then a variant is still produced, whose cterm equals the input (the no-op is recorded)
    assert variant.cterm == term(1)
    assert variant.producer is Producer.BOOSTER_SIMPLIFY
