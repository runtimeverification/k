from unittest import TestCase
from unittest.mock import patch

from pyk.kore.client import (
    DirectResult,
    DirectState,
    JsonRpcClient,
    KoreClient,
    StopReason,
)
from pyk.kore.syntax import DV, And, App, Bottom, SortApp, String, Top

intSort = SortApp('IntSort')


def intdv(n: int) -> DV:
    return DV(intSort, String(str(n)))


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
        MockClient.assert_called_with('localhost', 3000)
        self.assertEqual(self.client._client, self.mock)

    def assumeResponse(self, response):
        self.mock.request.return_value = response

    def assertRequest(self, method, **params):
        self.mock.request.assert_called_with(method, **params)

    def test_simplify(self):
        # Given
        pattern = And(intSort, Top(intSort), Top(intSort))
        params = {
            'state': {
                'format': 'KORE',
                'version': 1,
                'term': pattern.dict,
            },
        }
        response = {
            'state': {
                'format': 'KORE',
                'version': 1,
                'term': Top(intSort).dict,
            },
        }
        expected = Top(intSort)
        self.assumeResponse(response)

        # When
        actual = self.client.simplify(pattern)

        # Then
        self.assertRequest('simplify', **params)
        self.assertEqual(expected, actual)

    def test_implies(self):
        antecedent = Bottom(intSort)
        consequent = Top(intSort)
        params = {
            'antecedent': {
                'format': 'KORE',
                'version': 1,
                'term': antecedent.dict,
            },
            'consequent': {
                'format': 'KORE',
                'version': 1,
                'term': consequent.dict,
            },
        }
        response = {
            'satisfiable': True,
        }
        expected = (True, None, None)
        self.assumeResponse(response)

        # When
        actual = self.client.implies(antecedent, consequent)

        # Then
        self.assertRequest('implies', **params)
        self.assertEqual(expected, actual)

    def test_execute(self):
        pattern = App('IntAdd', (), (intdv(1), intdv(1)))
        params = {
            'state': {
                'format': 'KORE',
                'version': 1,
                'term': pattern.dict,
            },
        }
        response = {
            'states': [
                {
                    'state': {
                        'format': 'KORE',
                        'version': 1,
                        'term': intdv(2).dict
                    },
                    "depth": 1,
                }
            ],
            'reason': 'final-state',
        }
        expected = DirectResult(DirectState(intdv(2)), 1, StopReason.FINAL_STATE)
        self.assumeResponse(response)

        # When
        actual = self.client.execute(pattern)

        # Then
        self.assertRequest('execute', **params)
        self.assertEqual(expected, actual)
