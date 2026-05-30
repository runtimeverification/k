from __future__ import annotations

from unittest.mock import Mock

from pyk.cterm.symbolic import CTermExecute
from pyk.kcfg.explore import KCFGExplore
from pyk.kcfg.kcfg import NoProgress, Step

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
