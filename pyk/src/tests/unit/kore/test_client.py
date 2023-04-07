from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING
from unittest.mock import patch

import pytest

from pyk.kore.prelude import INT, int_dv
from pyk.kore.rpc import ImpliesResult, JsonRpcClient, KoreClient, State, StuckResult
from pyk.kore.syntax import And, App, Bottom, Module, Top

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any, Final
    from unittest.mock import Mock

    from pyk.kore.rpc import ExecuteResult
    from pyk.kore.syntax import Pattern

int_top = Top(INT)
int_bottom = Bottom(INT)


def kore(pattern: Pattern) -> dict[str, Any]:
    return {
        'format': 'KORE',
        'version': 1,
        'term': pattern.dict,
    }


class MockClient:
    mock: Mock

    def __init__(self, mock: Mock):
        self.mock = mock

    def assume_response(self, response: Any) -> None:
        self.mock.request.return_value = response

    def assert_request(self, method: str, **params: Any) -> None:
        self.mock.request.assert_called_with(method, **params)


@pytest.fixture
def mock_class() -> Iterator[Mock]:
    patcher = patch('pyk.kore.rpc.JsonRpcClient', spec=True)
    yield patcher.start()
    patcher.stop()


@pytest.fixture
def mock(mock_class: Mock) -> Mock:
    mock = mock_class.return_value
    assert isinstance(mock, JsonRpcClient)
    return mock  # type: ignore


@pytest.fixture
def rpc_client(mock: Mock) -> MockClient:
    return MockClient(mock)


@pytest.fixture
def kore_client(mock: Mock, mock_class: Mock) -> Iterator[KoreClient]:  # noqa: N803
    client = KoreClient('localhost', 3000)
    mock_class.assert_called_with('localhost', 3000, timeout=None, bug_report=None)
    assert client._client == mock
    yield client
    client.close()
    mock.close.assert_called()


EXECUTE_TEST_DATA: Final = (
    (
        App('IntAdd', (), (int_dv(1), int_dv(1))),
        {'state': kore(App('IntAdd', [], [int_dv(1), int_dv(1)]))},
        {
            'state': {'term': kore(int_dv(2)), 'substitution': kore(int_top), 'predicate': kore(int_top)},
            'depth': 1,
            'reason': 'stuck',
        },
        StuckResult(State(int_dv(2), int_top, int_top), 1),
    ),
)


@pytest.mark.parametrize('pattern,params,response,expected', EXECUTE_TEST_DATA, ids=count())
def test_execute(
    kore_client: KoreClient,
    rpc_client: MockClient,
    pattern: Pattern,
    params: dict[str, Any],
    response: dict[str, Any],
    expected: ExecuteResult,
) -> None:
    # Given
    rpc_client.assume_response(response)

    # When
    actual = kore_client.execute(pattern)

    # Then
    rpc_client.assert_request('execute', **params)
    assert actual == expected


IMPLIES_TEST_DATA: Final = (
    (
        int_bottom,
        int_top,
        {'antecedent': kore(int_bottom), 'consequent': kore(int_top)},
        {'satisfiable': True, 'implication': kore(int_top)},
        ImpliesResult(True, int_top, None, None),
    ),
)


@pytest.mark.parametrize('antecedent,consequent,params,response,expected', IMPLIES_TEST_DATA, ids=count())
def test_implies(
    kore_client: KoreClient,
    rpc_client: MockClient,
    antecedent: Pattern,
    consequent: Pattern,
    params: dict[str, Any],
    response: dict[str, Any],
    expected: ImpliesResult,
) -> None:
    # Given
    rpc_client.assume_response(response)

    # When
    actual = kore_client.implies(antecedent, consequent)

    # Then
    rpc_client.assert_request('implies', **params)
    assert actual == expected


SIMPLIFY_TEST_DATA: Final = (
    (
        And(INT, int_top, int_top),
        {'state': kore(And(INT, int_top, int_top))},
        {'state': kore(int_top)},
        int_top,
    ),
)


@pytest.mark.parametrize('pattern,params,response,expected', SIMPLIFY_TEST_DATA, ids=count())
def test_simplify(
    kore_client: KoreClient,
    rpc_client: MockClient,
    pattern: Pattern,
    params: dict[str, Any],
    response: dict[str, Any],
    expected: Pattern,
) -> None:
    # Given
    rpc_client.assume_response(response)

    # When
    actual = kore_client.simplify(pattern)

    # Then
    rpc_client.assert_request('simplify', **params)
    assert actual == expected


ADD_MODULE_TEST_DATA: Final = (
    (
        Module('HELLO'),
        {'module': 'module HELLO\nendmodule []'},
    ),
)


@pytest.mark.parametrize('module,params', ADD_MODULE_TEST_DATA, ids=count())
def test_add_module(
    kore_client: KoreClient,
    rpc_client: MockClient,
    module: Module,
    params: dict[str, Any],
) -> None:
    # Given
    rpc_client.assume_response([])

    # When
    kore_client.add_module(module)

    # Then
    rpc_client.assert_request('add-module', **params)
