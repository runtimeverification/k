from typing import Any, Dict
from unittest import TestCase
from unittest.mock import patch

from pyk.kore.client import ImpliesResult, JsonRpcClient, KoreClient, State, StuckResult
from pyk.kore.syntax import DV, And, App, Bottom, Pattern, SortApp, String, Top


class KoreClientTest(TestCase):
    mock: JsonRpcClient
    client: KoreClient

    def setUp(self):
        # Given
        patcher = patch('pyk.kore.client.JsonRpcClient', spec=True)
        MockClient = patcher.start()  # noqa: N806
        self.addCleanup(patcher.stop)
        self.mock = MockClient.return_value

        # When
        self.client = KoreClient('localhost', 3000)

        # Then
        self.assertIsInstance(self.mock, JsonRpcClient)
        MockClient.assert_called_with('localhost', 3000, timeout=None)
        self.assertEqual(self.client._client, self.mock)

    def tearDown(self):
        # When
        self.client.close()

        # Then
        self.mock.close.assert_called()

    def assumeResponse(self, response):  # noqa: N802
        self.mock.request.return_value = response

    def assertRequest(self, method, **params):  # noqa: N802
        self.mock.request.assert_called_with(method, **params)

    def test_execute(self):
        test_data = (
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

        for i, (pattern, params, response, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # Given
                self.assumeResponse(response)

                # When
                actual = self.client.execute(pattern)

                # Then
                self.assertRequest('execute', **params)
                self.assertEqual(expected, actual)

    def test_implies(self):
        test_data = (
            (
                int_bottom,
                int_top,
                {'antecedent': kore(int_bottom), 'consequent': kore(int_top)},
                {'satisfiable': True, 'implication': kore(int_top)},
                ImpliesResult(True, int_top, None, None),
            ),
        )

        for i, (antecedent, consequent, params, response, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # Given
                self.assumeResponse(response)

                # When
                actual = self.client.implies(antecedent, consequent)

                # Then
                self.assertRequest('implies', **params)
                self.assertEqual(expected, actual)

    def test_simplify(self):
        test_data = (
            (
                And(int_sort, int_top, int_top),
                {'state': kore(And(int_sort, int_top, int_top))},
                {'state': kore(int_top)},
                int_top,
            ),
        )

        for i, (pattern, params, response, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # Given
                self.assumeResponse(response)

                # When
                actual = self.client.simplify(pattern)

                # Then
                self.assertRequest('simplify', **params)
                self.assertEqual(expected, actual)


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
