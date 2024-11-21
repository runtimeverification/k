from __future__ import annotations

import json
from http.client import HTTPConnection
from threading import Thread
from time import sleep
from typing import Any

from pyk.rpc.rpc import JsonRpcServer, ServeRpcOptions
from pyk.testing import KRunTest


class StatefulKJsonRpcServer(JsonRpcServer):

    x: int = 42
    y: int = 43

    def __init__(self, options: ServeRpcOptions) -> None:
        super().__init__(options)

        self.register_method('get_x', self.exec_get_x)
        self.register_method('get_y', self.exec_get_y)
        self.register_method('set_x', self.exec_set_x)
        self.register_method('set_y', self.exec_set_y)
        self.register_method('add', self.exec_add)

    def exec_get_x(self) -> int:
        return self.x

    def exec_get_y(self) -> int:
        return self.y

    def exec_set_x(self, n: int) -> None:
        self.x = n

    def exec_set_y(self, n: int) -> None:
        self.y = n

    def exec_add(self) -> int:
        return self.x + self.y


class TestJsonRPCServer(KRunTest):

    def test_json_rpc_server(self) -> None:
        server = StatefulKJsonRpcServer(ServeRpcOptions({'port': 0}))

        def run_server() -> None:
            server.serve()

        def wait_until_server_is_up() -> None:
            while True:
                try:
                    server.port()
                    return
                except ValueError:
                    sleep(0.1)

        thread = Thread(target=run_server)
        thread.start()

        wait_until_server_is_up()

        http_client = HTTPConnection('localhost', server.port())
        rpc_client = SimpleClient(http_client)

        def wait_until_ready() -> None:
            while True:
                try:
                    rpc_client.request('get_x', [])
                except ConnectionRefusedError:
                    sleep(0.1)
                    continue
                break

        wait_until_ready()

        rpc_client.request('set_x', [123])
        res = rpc_client.request('get_x')
        assert res == 123

        rpc_client.request('set_y', [456])
        res = rpc_client.request('get_y')
        assert res == 456

        res = rpc_client.request('add', [])
        assert res == (123 + 456)

        res = rpc_client.batch_request(('set_x', [1]), ('set_y', [2]), ('add', []))
        assert len(res) == 3
        assert res[2]['result'] == 1 + 2

        server.shutdown()
        thread.join()


class SimpleClient:

    client: HTTPConnection
    _request_id: int = 0

    def __init__(self, client: HTTPConnection) -> None:
        self.client = client

    def request_id(self) -> int:
        self._request_id += 1
        return self._request_id

    def request(self, method: str, params: Any = None) -> Any:
        body = json.dumps({'jsonrpc': '2.0', 'method': method, 'params': params, 'id': self.request_id()})

        self.client.request('POST', '/', body)
        response = self.client.getresponse()
        result = json.loads(response.read())
        return result['result']

    def batch_request(self, *requests: tuple[str, Any]) -> list[Any]:
        body = json.dumps(
            [
                {'jsonrpc': '2.0', 'method': method, 'params': params, 'id': self.request_id()}
                for method, params in requests
            ]
        )

        self.client.request('POST', '/', body)
        response = self.client.getresponse()
        result = json.loads(response.read())
        return result
