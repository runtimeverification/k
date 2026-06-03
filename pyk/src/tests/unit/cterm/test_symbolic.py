from __future__ import annotations

from typing import TYPE_CHECKING
from unittest.mock import Mock

from pyk.cterm.symbolic import CTermSymbolic
from pyk.kast.prelude.ml import mlTop
from pyk.kore.prelude import int_dv
from pyk.kore.rpc import State, StuckResult

if TYPE_CHECKING:
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


def test_execute_forwards_haskell_logging() -> None:
    # Given
    kore_client, cts = _mock_client_cts(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))
    dummy: CTerm = Mock()

    # When
    cts.execute(dummy, haskell_logging=True)

    # Then the per-call flag reaches the underlying KoreClient.execute
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['haskell_logging'] is True


def test_execute_default_leaves_haskell_logging_off() -> None:
    # Given
    kore_client, cts = _mock_client_cts(StuckResult(state=State(term=int_dv(2)), depth=1, logs=()))
    dummy: CTerm = Mock()

    # When called with defaults
    cts.execute(dummy)

    # Then logging is left untouched (None preserves today's behaviour)
    _args, kwargs = kore_client.execute.call_args
    assert kwargs['haskell_logging'] is None
