"""Unit tests for the caller-supplied `client_label` on JsonRpcClient / KoreClient.

The label is stamped on every outgoing request-id (`{label}-NNN`) so booster's
per-line `{request: ...}` context self-identifies the caller (typically the
claim being discharged).  `set_client_label(label)` mutates the prefix for all
subsequent requests; in normal pyk use, APRProver/ImpliesProver invoke this
automatically per proof so consumers never touch the API directly.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING
from unittest.mock import patch

import pytest

from pyk.kore.rpc import JsonRpcClient, KoreClient, SingleSocketTransport

if TYPE_CHECKING:
    from collections.abc import Iterator
    from unittest.mock import Mock


@pytest.fixture
def mock_class() -> Iterator[Mock]:
    patcher = patch('pyk.kore.rpc.SingleSocketTransport', spec=True)
    yield patcher.start()
    patcher.stop()


@pytest.fixture
def mock(mock_class: Mock) -> Mock:
    mock = mock_class.return_value
    assert isinstance(mock, SingleSocketTransport)
    return mock  # type: ignore


def _wire_capture(mock: Mock) -> list[dict]:
    """Capture every outgoing payload and echo a success response."""
    captured: list[dict] = []

    def respond(req: str, req_id: str, method_name: str) -> str:
        payload = json.loads(req)
        captured.append(payload)
        return json.dumps({'jsonrpc': '2.0', 'id': payload['id'], 'result': {}})

    mock.request.side_effect = respond
    return captured


def test_default_label_uses_object_id(mock: Mock) -> None:
    """Without a client_label, the request-id prefix is str(id(self)) — byte-stable with the legacy path."""
    captured = _wire_capture(mock)
    client = JsonRpcClient('localhost', 3000)
    expected_prefix = str(id(client))

    client.request('execute')
    client.request('simplify')

    assert [p['id'] for p in captured] == [f'{expected_prefix}-001', f'{expected_prefix}-002']


def test_construction_label_is_used_as_prefix(mock: Mock) -> None:
    captured = _wire_capture(mock)
    client = JsonRpcClient('localhost', 3000, client_label='LEMMAS-SPEC.range-31')

    client.request('execute')
    client.request('simplify')

    assert [p['id'] for p in captured] == ['LEMMAS-SPEC.range-31-001', 'LEMMAS-SPEC.range-31-002']


def test_set_client_label_swaps_prefix_for_subsequent_requests(mock: Mock) -> None:
    captured = _wire_capture(mock)
    client = JsonRpcClient('localhost', 3000, client_label='claim-A')

    client.request('execute')
    client.set_client_label('claim-B')
    client.request('simplify')
    client.request('implies')

    assert [p['id'] for p in captured] == ['claim-A-001', 'claim-B-002', 'claim-B-003']


def test_set_client_label_persists_no_restoration(mock: Mock) -> None:
    """The setter is permanent — there is no enclosing scope or restoration semantics."""
    captured = _wire_capture(mock)
    client = JsonRpcClient('localhost', 3000, client_label='outer')

    client.set_client_label('inner')
    client.request('execute')
    client.request('simplify')

    assert [p['id'] for p in captured] == ['inner-001', 'inner-002']


def test_kore_client_forwards_client_label(mock: Mock) -> None:
    """KoreClient(client_label=...) plumbs through to the underlying JsonRpcClient."""
    captured = _wire_capture(mock)
    kore_client = KoreClient('localhost', 3000, client_label='claim-X')

    assert kore_client._client._default_client._client_label == 'claim-X'

    kore_client._client._default_client.request('execute')
    assert captured[-1]['id'] == 'claim-X-001'


def test_kore_client_set_client_label_forwards_to_underlying_clients(mock: Mock) -> None:
    captured = _wire_capture(mock)
    kore_client = KoreClient('localhost', 3000, client_label='construction-default')

    kore_client.set_client_label('claim-A')
    kore_client._client._default_client.request('execute')
    kore_client.set_client_label('claim-B')
    kore_client._client._default_client.request('simplify')

    assert [p['id'] for p in captured] == ['claim-A-001', 'claim-B-002']
