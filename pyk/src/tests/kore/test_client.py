from typing import Any, Dict
from unittest import TestCase
from unittest.mock import patch

from pyk.kore.client import JsonRpcClient, KoreClient, State, StuckResult
from pyk.kore.syntax import DV, And, App, Bottom, Pattern, SortApp, String, Top


class KoreClientTest(TestCase):
    mock: JsonRpcClient
    client: KoreClient

    def setUp(self):
        # Given
        patcher = patch('pyk.kore.client.JsonRpcClient', spec=True)
        MockClient = patcher.start()
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

    def assumeResponse(self, response):
        self.mock.request.return_value = response

    def assertRequest(self, method, **params):
        self.mock.request.assert_called_with(method, **params)

    def test_execute(self):
        test_data = (
            (
                App('IntAdd', (), (intDV(1), intDV(1))),
                {'state': kore(App('IntAdd', [], [intDV(1), intDV(1)]))},
                {
                    'state': {'term': kore(intDV(2)), 'substitution': kore(intTop), 'predicate': kore(intTop)},
                    'depth': 1,
                    'reason': 'stuck',
                },
                StuckResult(State(intDV(2), intTop, intTop), 1),
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
                intBottom,
                intTop,
                {'antecedent': kore(intBottom), 'consequent': kore(intTop)},
                {'satisfiable': True},
                (True, None, None),
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
                And(intSort, intTop, intTop),
                {'state': kore(And(intSort, intTop, intTop))},
                {'state': kore(intTop)},
                intTop,
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


intSort = SortApp('IntSort')
intTop = Top(intSort)
intBottom = Bottom(intSort)


def intDV(n: int) -> DV:
    return DV(intSort, String(str(n)))


def kore(pattern: Pattern) -> Dict[str, Any]:
    return {
        'format': 'KORE',
        'version': 1,
        'term': pattern.dict,
    }
