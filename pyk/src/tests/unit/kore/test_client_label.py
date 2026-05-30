from __future__ import annotations

import json
from contextvars import copy_context
from typing import TYPE_CHECKING
from unittest.mock import MagicMock, patch

from pyk.kore.rpc import JsonRpcClient, client_label

if TYPE_CHECKING:
    from typing import Any


# Every test below is wrapped in `_run_isolated` so its mutations to the module-level
# `client_label` ContextVar are confined to a private copy of the current context.
# Without this, cross-test contamination would be possible if pytest were to reorder
# or run tests in the same context.


def _mock_transport() -> MagicMock:
    """Mock transport that echoes the request id back in its response, satisfying JsonRpcClient._check."""
    transport = MagicMock()

    def _echo(req: str, req_id: str, _method: str) -> str:
        return json.dumps({'jsonrpc': '2.0', 'id': req_id, 'result': {}})

    transport.request.side_effect = _echo
    return transport


def _captured_ids(transport: MagicMock) -> list[str]:
    """Pull the JSON-RPC `id` off every recorded transport.request call."""
    return [json.loads(call.args[0])['id'] for call in transport.request.call_args_list]


def _new_client() -> tuple[JsonRpcClient, MagicMock]:
    transport = _mock_transport()
    with patch.object(JsonRpcClient, '_create_transport', return_value=transport):
        client = JsonRpcClient('localhost', 0)
    return client, transport


def _run_isolated(body: Any) -> None:
    """Run `body` inside a fresh copy of the current context so contextvar writes don't leak."""
    copy_context().run(body)


def test_default_prefix_uses_id_of_client() -> None:
    """No label set → request id is `{id(client)}-001`, preserving prior behavior byte-for-byte."""

    def body() -> None:
        client, transport = _new_client()
        client.request('execute', state={})
        assert _captured_ids(transport) == [f'{id(client)}-001']

    _run_isolated(body)


def test_set_label_prefixes_subsequent_request() -> None:
    """`client_label.set('foo')` → next request id is `foo-001`."""

    def body() -> None:
        client, transport = _new_client()
        client_label.set('proof-A')
        client.request('execute', state={})
        assert _captured_ids(transport) == ['proof-A-001']

    _run_isolated(body)


def test_label_persists_across_requests_and_counter_increments() -> None:
    """A single `set` covers every subsequent request on the same thread; counter keeps incrementing."""

    def body() -> None:
        client, transport = _new_client()
        client_label.set('proof-B')
        client.request('execute', state={})
        client.request('simplify', state={})
        client.request('implies', antecedent={}, consequent={})
        assert _captured_ids(transport) == ['proof-B-001', 'proof-B-002', 'proof-B-003']

    _run_isolated(body)


def test_token_reset_restores_prior_label() -> None:
    """`client_label.reset(token)` returns the contextvar to its prior value — enables scoped overrides."""

    def body() -> None:
        client, transport = _new_client()
        client_label.set('outer')
        token = client_label.set('inner')
        client.request('execute', state={})
        client_label.reset(token)
        client.request('execute', state={})
        assert _captured_ids(transport) == ['inner-001', 'outer-002']

    _run_isolated(body)
