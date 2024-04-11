from __future__ import annotations

from threading import Thread
from time import sleep

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KSort, KToken
from pyk.kast.manip import set_cell
from pyk.kore.rpc import JsonRpcClient, TransportType
from pyk.ktool.krun import KRun
from pyk.rpc.rpc import JsonRpcServer, ServeRpcOptions
from pyk.testing import KRunTest


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


class TestJsonRPCServer(KRunTest):
    KOMPILE_DEFINITION = """
        module JSON-RPC-EXAMPLE
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
        server = StatefulKJsonRpcServer(ServeRpcOptions({'definition_dir': krun.definition_dir}))

        def run_server() -> None:
            server.serve()

        process = Thread(target=run_server)
        process.start()

        rpc_client = JsonRpcClient('localhost', 56601, transport=TransportType.HTTP)

        def wait_until_ready() -> None:
            while True:
                try:
                    rpc_client.request('get_x')
                except ConnectionRefusedError:
                    sleep(1)
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
        process.join()
