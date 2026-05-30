from __future__ import annotations

import json
from itertools import count
from threading import Barrier, Thread
from typing import TYPE_CHECKING
from unittest.mock import patch

import pytest

from pyk.kore.prelude import int_dv
from pyk.kore.rpc import KoreClient, SingleSocketTransport, _last_request_id, client_label
from pyk.kore.syntax import App

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Final
    from unittest.mock import Mock

    from pyk.kore.syntax import Pattern


class MockTransport:
    mock: Mock

    def __init__(self, mock: Mock):
        self.mock = mock

    def assume_response(self, response: str) -> None:
        self.mock.request.return_value = response


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


@pytest.fixture
def transport(mock: Mock) -> MockTransport:
    return MockTransport(mock)


@pytest.fixture
def kore_client(mock: Mock, mock_class: Mock) -> Iterator[KoreClient]:  # noqa: N803
    client = KoreClient('localhost', 3000)
    mock_class.assert_called_with('localhost', 3000, timeout=None)
    assert client._client._default_client._transport == mock
    yield client
    client.close()
    mock.close.assert_called()


EXCEPTION_TEST_DATA: Final = ((App('IntAdd', (), (int_dv(1), int_dv(1))), '', RuntimeError('Empty response received')),)


@pytest.mark.parametrize('pattern,response,expected', EXCEPTION_TEST_DATA, ids=count())
def test_exceptions(
    kore_client: KoreClient,
    transport: MockTransport,
    pattern: Pattern,
    response: str,
    expected: Exception,
) -> None:
    # Given
    transport.assume_response(response)

    with pytest.raises(Exception) as client_err:
        # When
        kore_client.execute(pattern)

    # Then
    assert client_err.type is type(expected)
    assert str(client_err.value) == str(expected)


def test_last_request_id_tracks_issued_id(kore_client: KoreClient, transport: MockTransport) -> None:
    # Given a known client label, the issued id is deterministic: f'{label}-001'.
    token = client_label.set('claim-x')
    try:
        transport.assume_response(json.dumps({'jsonrpc': '2.0', 'id': 'claim-x-001', 'result': {'k': 'v'}}))

        # When (drive the underlying JsonRpcClient directly, bypassing Kore result parsing)
        out = kore_client._client._default_client.request('simplify', state={'x': 1})

        # Then
        assert out == {'k': 'v'}
        assert kore_client.last_request_id == 'claim-x-001'
    finally:
        client_label.reset(token)


def test_last_request_id_is_thread_local(kore_client: KoreClient) -> None:
    # Each thread must read back its own last-request id, never another thread's.
    seen: dict[str, str | None] = {}
    barrier = Barrier(2)

    def worker(name: str) -> None:
        _last_request_id.value = name
        barrier.wait()  # both threads have set their value before either reads
        seen[name] = kore_client.last_request_id

    t1 = Thread(target=worker, args=('a',))
    t2 = Thread(target=worker, args=('b',))
    t1.start()
    t2.start()
    t1.join()
    t2.join()

    assert seen == {'a': 'a', 'b': 'b'}
