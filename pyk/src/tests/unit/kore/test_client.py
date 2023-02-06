from itertools import count
from typing import Any, Dict, Final, Iterator
from unittest.mock import Mock, patch

import pytest

from pyk.kore.rpc import ExecuteResult, ImpliesResult, JsonRpcClient, KoreClient, State, StuckResult
from pyk.kore.syntax import DV, And, App, Bottom, Pattern, SortApp, String, Top


class MockClient:
    mock: Mock

    def __init__(self, mock: Mock):
        self.mock = mock

    def assume_response(self, response: Dict[str, Any]) -> None:
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


int_sort = SortApp('IntSort')
int_top = Top(int_sort)
int_bottom = Bottom(int_sort)


def int_dv(n: int) -> DV:
    return DV(int_sort, String(str(n)))


def kore(pattern: Pattern) -> Dict[str, Any]:
    return {
        'format': 'KORE',
        'version': 1,
        'term': pattern.dict,
    }


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

IMPLIES_TEST_DATA: Final = (
    (
        int_bottom,
        int_top,
        {'antecedent': kore(int_bottom), 'consequent': kore(int_top)},
        {'satisfiable': True, 'implication': kore(int_top)},
        ImpliesResult(True, int_top, None, None),
    ),
)

SIMPLIFY_TEST_DATA: Final = (
    (
        And(int_sort, int_top, int_top),
        {'state': kore(And(int_sort, int_top, int_top))},
        {'state': kore(int_top)},
        int_top,
    ),
)


@pytest.mark.parametrize('pattern,params,response,expected', EXECUTE_TEST_DATA, ids=count())
def test_execute(
    kore_client: KoreClient,
    rpc_client: MockClient,
    pattern: Pattern,
    params: Dict[str, Any],
    response: Dict[str, Any],
    expected: ExecuteResult,
) -> None:
    # Given
    rpc_client.assume_response(response)

    # When
    actual = kore_client.execute(pattern)

    # Then
    rpc_client.assert_request('execute', **params)
    assert actual == expected


@pytest.mark.parametrize('antecedent,consequent,params,response,expected', IMPLIES_TEST_DATA, ids=count())
def test_implies(
    kore_client: KoreClient,
    rpc_client: MockClient,
    antecedent: Pattern,
    consequent: Pattern,
    params: Dict[str, Any],
    response: Dict[str, Any],
    expected: ImpliesResult,
) -> None:
    # Given
    rpc_client.assume_response(response)

    # When
    actual = kore_client.implies(antecedent, consequent)

    # Then
    rpc_client.assert_request('implies', **params)
    assert actual == expected


@pytest.mark.parametrize('pattern,params,response,expected', SIMPLIFY_TEST_DATA, ids=count())
def test_simplify(
    kore_client: KoreClient,
    rpc_client: MockClient,
    pattern: Pattern,
    params: Dict[str, Any],
    response: Dict[str, Any],
    expected: Pattern,
) -> None:
    # Given
    rpc_client.assume_response(response)

    # When
    actual = kore_client.simplify(pattern)

    # Then
    rpc_client.assert_request('simplify', **params)
    assert actual == expected
