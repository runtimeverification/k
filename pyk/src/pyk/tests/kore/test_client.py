from unittest import TestCase
from unittest.mock import patch

from pyk.kore.client import JsonRpcClient, KoreClient
from pyk.kore.syntax import SortApp, Top


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

    def test(self):
        # Given
        top_state = {
            'state': {
                'format': 'KORE',
                'version': 1,
                'term': {
                    'tag': 'Top',
                    'sort': {
                        'tag': 'SortApp',
                        'name': 'KSort',
                        'args': [],
                    },
                },
            },
        }
        self.mock.request.return_value = top_state

        # When
        res = self.client.simplify(Top(SortApp('KSort')))

        # Then
        self.mock.request.assert_called_with('simplify', **top_state)
        self.assertEqual(res, Top(SortApp('KSort')))
