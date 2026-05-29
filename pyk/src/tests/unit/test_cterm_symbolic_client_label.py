"""Unit tests for the set_client_label plumbing on CTermSymbolic.

CTermSymbolic.set_client_label(label) is the setter that APRProver/ImpliesProver
call automatically per proof so booster's per-line `{request: ...}` context
self-identifies the claim driving the work.  Consumers normally do not call
this directly.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, cast
from unittest.mock import MagicMock, patch

import pytest

from pyk.cterm.symbolic import CTermSymbolic
from pyk.kore.rpc import KoreClient, SingleSocketTransport

if TYPE_CHECKING:
    from collections.abc import Iterator
    from unittest.mock import Mock

    from pyk.kast.outer import KDefinition


@pytest.fixture
def mock_class() -> Iterator[Mock]:
    patcher = patch('pyk.kore.rpc.SingleSocketTransport', spec=True)
    yield patcher.start()
    patcher.stop()


@pytest.fixture
def mock(mock_class: Mock) -> Mock:
    m = mock_class.return_value
    assert isinstance(m, SingleSocketTransport)
    return m  # type: ignore


def _wire_capture(mock: Mock) -> list[dict]:
    captured: list[dict] = []

    def respond(req: str, req_id: str, method_name: str) -> str:
        payload = json.loads(req)
        captured.append(payload)
        return json.dumps({'jsonrpc': '2.0', 'id': payload['id'], 'result': {}})

    mock.request.side_effect = respond
    return captured


def _make_cterm_symbolic(client_label: str | None) -> tuple[CTermSymbolic, KoreClient]:
    client = KoreClient('localhost', 3000, client_label=client_label)
    # The definition is held by CTermSymbolic but never invoked by set_client_label,
    # so a MagicMock satisfies the runtime requirement.
    cterm = CTermSymbolic(client, cast('KDefinition', MagicMock()))
    return cterm, client


def test_cterm_symbolic_set_client_label_swaps_prefix(mock: Mock) -> None:
    captured = _wire_capture(mock)
    cterm, client = _make_cterm_symbolic(client_label='construction-default')

    client._client._default_client.request('execute')
    cterm.set_client_label('claim-A')
    client._client._default_client.request('simplify')
    cterm.set_client_label('claim-B')
    client._client._default_client.request('implies')

    assert [p['id'] for p in captured] == [
        'construction-default-001',
        'claim-A-002',
        'claim-B-003',
    ]


def test_cterm_symbolic_serves_multiple_claims_in_sequence(mock: Mock) -> None:
    """One CTermSymbolic discharging two claims in turn — prover stamps each label once."""
    captured = _wire_capture(mock)
    cterm, client = _make_cterm_symbolic(client_label='unused-default')

    cterm.set_client_label('claim-A')
    client._client._default_client.request('execute')
    client._client._default_client.request('simplify')
    cterm.set_client_label('claim-B')
    client._client._default_client.request('execute')

    assert [p['id'] for p in captured] == [
        'claim-A-001',
        'claim-A-002',
        'claim-B-003',
    ]
