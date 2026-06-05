from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING
from unittest.mock import patch

import pytest

from pyk.kore.prelude import int_dv
from pyk.kore.rpc import KoreClient, SingleSocketTransport
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
