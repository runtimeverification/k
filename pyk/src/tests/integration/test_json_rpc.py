from __future__ import annotations

import json
from http.client import HTTPConnection
from threading import Thread
from time import sleep
from typing import TYPE_CHECKING

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KSort, KToken
from pyk.kast.manip import set_cell
from pyk.kore.rpc import JsonRpcClient, TransportType
from pyk.ktool.krun import KRun
from pyk.rpc.rpc import JsonRpcServer, ServeRpcOptions
from pyk.testing import KRunTest

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any


class StatefulKJsonRpcServer(JsonRpcServer):
    krun: KRun
    cterm: CTerm

    def __init__(self, options: ServeRpcOptions) -> None:
        super().__init__(options)

        self.register_method('get_x', self.exec_get_x)
        self.register_method('get_y', self.exec_get_y)
        self.register_method('set_x', self.exec_set_x)
        self.register_method('set_y', self.exec_set_y)
        self.register_method('add', self.exec_add)

        if not options.definition_dir:
            raise ValueError('Must specify a definition dir with --definition')
        self.krun = KRun(options.definition_dir)
        self.cterm = CTerm.from_kast(self.krun.definition.init_config(KSort('GeneratedTopCell')))

    def exec_get_x(self) -> int:
        x_cell = self.cterm.cell('X_CELL')
        assert type(x_cell) is KToken
        return int(x_cell.token)

    def exec_get_y(self) -> int:
        y_cell = self.cterm.cell('Y_CELL')
        assert type(y_cell) is KToken
        return int(y_cell.token)

    def exec_set_x(self, n: int) -> None:
        self.cterm = CTerm.from_kast(
            set_cell(self.cterm.config, 'X_CELL', KToken(token=str(n), sort=KSort(name='Int')))
        )

    def exec_set_y(self, n: int) -> None:
        self.cterm = CTerm.from_kast(
            set_cell(self.cterm.config, 'Y_CELL', KToken(token=str(n), sort=KSort(name='Int')))
        )

    def exec_add(self) -> int:
        x = self.cterm.cell('X_CELL')
        y = self.cterm.cell('Y_CELL')
        self.cterm = CTerm.from_kast(set_cell(self.cterm.config, 'K_CELL', KApply('_+Int_', [x, y])))

        pattern = self.krun.kast_to_kore(self.cterm.config, sort=KSort('GeneratedTopCell'))
        output_kore = self.krun.run_pattern(pattern)
        self.cterm = CTerm.from_kast(self.krun.kore_to_kast(output_kore))
        k_cell = self.cterm.cell('K_CELL')
        if type(k_cell) is KSequence:
            assert len(k_cell.items) == 1
            k_cell = k_cell.items[0]

        assert type(k_cell) is KToken
        return int(k_cell.token)


class TestJsonKRPCServer(KRunTest):
    KOMPILE_DEFINITION = """
        module JSON-RPC-EXAMPLE-SYNTAX
          imports INT-SYNTAX
        endmodule

        module JSON-RPC-EXAMPLE
          imports JSON-RPC-EXAMPLE-SYNTAX
          imports INT

          configuration
            <example>
              <k> $PGM </k>
              <x> 0:Int </x>
              <y> 0:Int </y>
            </example>
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'JSON-RPC-EXAMPLE'
    KOMPILE_BACKEND = 'llvm'

    def test_json_rpc_server(self, krun: KRun) -> None:
        server = StatefulKJsonRpcServer(ServeRpcOptions({'definition_dir': krun.definition_dir, 'port': 0}))

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

        rpc_client = JsonRpcClient('localhost', server.port(), transport=TransportType.HTTP)

        def wait_until_ready() -> None:
            while True:
                try:
                    rpc_client.request('get_x')
                except ConnectionRefusedError:
                    sleep(0.1)
                    continue
                break

        wait_until_ready()

        rpc_client.request('set_x', n=123)
        res = rpc_client.request('get_x')
        assert res == 123

        rpc_client.request('set_y', n=456)
        res = rpc_client.request('get_y')
        assert res == 456

        res = rpc_client.request('add')
        assert res == (123 + 456)

        server.shutdown()
        thread.join()


class StatefulJsonRpcServer(JsonRpcServer):

    x: int = 42
    y: int = 43

    def __init__(self, options: ServeRpcOptions) -> None:
        super().__init__(options)

        self.register_method('get_x', self.exec_get_x)
        self.register_method('get_y', self.exec_get_y)
        self.register_method('set_x', self.exec_set_x)
        self.register_method('set_y', self.exec_set_y)
        self.register_method('add', self.exec_add)
        self.register_method('streaming', self.exec_streaming)

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

    def exec_streaming(self) -> Iterator[bytes]:
        yield b'{'
        yield b'"foo": "bar"'
        yield b'}'


class TestJsonRPCServer(KRunTest):

    def test_json_rpc_server(self) -> None:
        server = StatefulJsonRpcServer(ServeRpcOptions({'port': 0}))

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

        res = rpc_client.request('streaming', [])
        assert res == {'foo': 'bar'}

        res = rpc_client.batch_request(('streaming', []), ('set_x', [10]), ('streaming', []))
        assert len(res) == 3
        assert res[0]['result'] == {'foo': 'bar'}
        assert res[1]['result'] == 10
        assert res[2]['result'] == {'foo': 'bar'}

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
