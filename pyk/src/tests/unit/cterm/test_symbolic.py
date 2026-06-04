from __future__ import annotations

import json
from typing import TYPE_CHECKING
from unittest.mock import Mock, patch

from pyk.cterm.symbolic import HASKELL_LOGGING_ENTRIES, CTermSymbolic, cterm_symbolic
from pyk.kast.prelude.ml import mlTop
from pyk.kore.prelude import int_dv
from pyk.kore.rpc import State, StuckResult

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
