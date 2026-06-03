from __future__ import annotations

import json
from typing import TYPE_CHECKING
from unittest.mock import Mock, patch

import pytest

from pyk.cterm.symbolic import HASKELL_LOGGING_ENTRIES, CTermSymbolic, cterm_symbolic
from pyk.kast.prelude.ml import mlTop
from pyk.kore.prelude import int_dv
from pyk.kore.rpc import AbortedResult, ImpliesResult, State, StuckResult

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.cterm import CTerm


def _mock_client_cts(response: object) -> tuple[Mock, CTermSymbolic]:
    """Build a `CTermSymbolic` whose backend returns ``response`` and whose Kast<->Kore
    conversions are stubbed, returning the backend `Mock` so a test can inspect call args.
    """
    kore_client = Mock()
    kore_client.execute.return_value = response
    cts = CTermSymbolic(kore_client, Mock())
    cts.kast_to_kore = Mock(return_value=Mock())  # type: ignore[method-assign]
    cts.kore_to_kast = Mock(return_value=mlTop())  # type: ignore[method-assign]
    return kore_client, cts


def _cterm_symbolic(response: object) -> CTermSymbolic:
    """Build a `CTermSymbolic` whose backend returns ``response`` and whose Kast<->Kore
    conversions are stubbed, so ``execute`` can be exercised without a real ``KDefinition``.
    """
    kore_client = Mock()
    kore_client.execute.return_value = response
    cts = CTermSymbolic(kore_client, Mock())
    # The conversions need a real definition; stub them. ``kore_to_kast`` returns ML-top so
    # ``CTerm.from_kast`` yields ``CTerm.top()`` (no config cell required).
    cts.kast_to_kore = Mock(return_value=Mock())  # type: ignore[method-assign]
    cts.kore_to_kast = Mock(return_value=mlTop())  # type: ignore[method-assign]
    return cts


def test_execute_on_requests_configured_entries() -> None:
    # Given
    kore_client, cts = _mock_client_cts(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))
    dummy: CTerm = Mock()

    # When the per-call flag turns logging on
    cts.execute(dummy, haskell_logging=True)

    # Then the configured entry set (the canonical default here) is what reaches KoreClient.execute
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['haskell_logging'] == HASKELL_LOGGING_ENTRIES


def test_execute_honors_custom_entry_set() -> None:
    # Given a CTermSymbolic configured with a custom entry set
    kore_client = Mock()
    kore_client.execute.return_value = StuckResult(state=State(term=int_dv(2)), depth=1, logs=())
    cts = CTermSymbolic(kore_client, Mock(), haskell_log_entries=['Rewrite', 'DebugApplyEquation'])
    cts.kast_to_kore = Mock(return_value=Mock())  # type: ignore[method-assign]
    cts.kore_to_kast = Mock(return_value=mlTop())  # type: ignore[method-assign]

    # When
    cts.execute(Mock(), haskell_logging=True)

    # Then exactly that set is requested
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['haskell_logging'] == ('Rewrite', 'DebugApplyEquation')


def test_execute_default_leaves_haskell_logging_off() -> None:
    # Given
    kore_client, cts = _mock_client_cts(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))
    dummy: CTerm = Mock()

    # When called with defaults
    cts.execute(dummy)

    # Then logging is left untouched (None preserves today's behaviour)
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['haskell_logging'] is None


def _log_dir_cts(response: object, haskell_log_dir: Path) -> tuple[Mock, CTermSymbolic]:
    kore_client = Mock()
    kore_client.execute.return_value = response
    cts = CTermSymbolic(kore_client, Mock(), haskell_log_dir=haskell_log_dir)
    cts.kast_to_kore = Mock(return_value=Mock())  # type: ignore[method-assign]
    cts.kore_to_kast = Mock(return_value=mlTop())  # type: ignore[method-assign]
    return kore_client, cts


def test_execute_writes_haskell_log_bundle(tmp_path: Path) -> None:
    # Given a configured log dir and a response carrying a per-request bundle
    entry = {'context': ['Proxy'], 'message': 'simplifying'}
    response = StuckResult(state=State(term=int_dv(2)), depth=1, logs=(), haskell_log_entries=(entry,))
    kore_client, cts = _log_dir_cts(response, tmp_path)
    kore_client.last_request_id = 'proof-007'

    # When
    cts.execute(Mock())

    # Then logging is requested and the bundle lands in <dir>/<request_id>.jsonl, one JSON value per line
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['haskell_logging'] == HASKELL_LOGGING_ENTRIES
    log_file = tmp_path / 'proof-007.jsonl'
    assert json.loads(log_file.read_text().strip()) == entry


def test_execute_writes_no_file_when_bundle_absent(tmp_path: Path) -> None:
    # Given a configured log dir but a response with no bundle
    response = StuckResult(state=State(term=int_dv(2)), depth=1, logs=(), haskell_log_entries=None)
    kore_client, cts = _log_dir_cts(response, tmp_path)
    kore_client.last_request_id = 'proof-008'

    # When
    cts.execute(Mock())

    # Then nothing is written
    assert not list(tmp_path.iterdir())


def test_cterm_symbolic_forwards_custom_entry_set() -> None:
    # Given a caller that overrides the per-request entry set through the factory
    with patch('pyk.cterm.symbolic.KoreClient'):
        with cterm_symbolic(
            definition=Mock(),
            definition_dir=Mock(),
            start_server=False,
            port=1,
            haskell_log_entries=['Rewrite', 'DebugApplyEquation'],
        ) as cts:
            # Then the built CTermSymbolic requests exactly that set
            assert cts._haskell_log_entries == ('Rewrite', 'DebugApplyEquation')


def test_cterm_symbolic_defaults_to_canonical_entry_set() -> None:
    # Given no override
    with patch('pyk.cterm.symbolic.KoreClient'):
        with cterm_symbolic(definition=Mock(), definition_dir=Mock(), start_server=False, port=1) as cts:
            # Then the canonical default is used
            assert cts._haskell_log_entries == HASKELL_LOGGING_ENTRIES


def test_execute_raises_on_abort_by_default() -> None:
    # Given
    cts = _cterm_symbolic(AbortedResult(state=State(term=int_dv(1)), depth=0, unknown_predicate=None, logs=()))
    dummy: CTerm = Mock()

    # Then
    with pytest.raises(ValueError, match='aborted state'):
        cts.execute(dummy)


def test_execute_surfaces_abort_when_not_raising() -> None:
    # Given
    cts = _cterm_symbolic(AbortedResult(state=State(term=int_dv(1)), depth=3, unknown_predicate=None, logs=()))
    dummy: CTerm = Mock()

    # When
    result = cts.execute(dummy, raise_on_aborted=False)

    # Then
    assert result.aborted
    assert result.depth == 3
    assert not result.vacuous


def test_execute_not_aborted_on_normal_result() -> None:
    # Given
    cts = _cterm_symbolic(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))
    dummy: CTerm = Mock()

    # When
    result = cts.execute(dummy, raise_on_aborted=False)

    # Then
    assert not result.aborted
    assert result.depth == 1


def test_execute_forwards_per_call_params() -> None:
    # Given
    kore_client, cts = _mock_client_cts(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))

    # When
    cts.execute(Mock(), booster_only_simplify=True, haskell_logging=True, raise_on_aborted=False)

    # Then the per-call flags reach the underlying KoreClient.execute; the haskell_logging bool is
    # resolved to the configured entry set on the way through.
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['booster_only_simplify'] is True
    assert kwargs['haskell_logging'] == HASKELL_LOGGING_ENTRIES


def test_execute_default_params_preserve_current_call() -> None:
    # Given
    kore_client, cts = _mock_client_cts(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))

    # When called with defaults
    cts.execute(Mock())

    # Then booster-only falls back to the instance default (False) and logging is off
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['booster_only_simplify'] is False
    assert kwargs['haskell_logging'] is None


@pytest.mark.parametrize('indeterminate', [True, False, None], ids=['true', 'false', 'absent'])
def test_implies_surfaces_indeterminate(indeterminate: bool | None) -> None:
    # Given a falsifiable implication carrying the backend `indeterminate` flag
    kore_client = Mock()
    kore_client.implies.return_value = ImpliesResult(
        valid=False,
        implication=Mock(),
        substitution=None,
        predicate=None,
        logs=(),
        indeterminate=indeterminate,
    )
    cts = CTermSymbolic(kore_client, Mock())
    cts.kast_to_kore = Mock(return_value=Mock())  # type: ignore[method-assign]
    # Stub CTerm operands: no free vars (so no consequent binding), arbitrary kast.
    antecedent: CTerm = Mock(free_vars=frozenset())
    consequent: CTerm = Mock(free_vars=frozenset())

    # When
    result = cts.implies(antecedent, consequent)

    # Then
    assert result.csubst is None
    assert result.indeterminate is indeterminate
