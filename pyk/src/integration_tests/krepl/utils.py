from subprocess import Popen
from typing import Any, ContextManager, List
from unittest import TestCase

from pyk.krepl.client import KReplClient

from ..utils import free_port_on_host, wait_for_port


class KReplProc(ContextManager['KReplProc']):
    _proc: Popen

    def __init__(self, *args: str):
        self._proc = Popen(('krepl-server',) + args)

    def __enter__(self) -> 'KReplProc':
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    def close(self) -> None:
        self._proc.terminate()
        self._proc.wait()

    @property
    def pid(self) -> int:
        return self._proc.pid


class KReplTest(TestCase):
    KREPL_LOGLEVEL: str = 'error'

    _server: KReplProc
    client: KReplClient

    def setUp(self) -> None:
        port = free_port_on_host()

        args: List[str] = []
        args += ['--port', str(port)]
        args += ['--loglevel', self.KREPL_LOGLEVEL]

        self._server = KReplProc(*args)
        wait_for_port(port)
        self.client = KReplClient(port)

    def tearDown(self) -> None:
        self._server.close()
