import time
from socket import AF_INET, SOCK_STREAM, socket
from subprocess import Popen
from typing import Any, ContextManager, List
from unittest import TestCase

from pyk.krepl.client import KReplClient
from pyk.krepl.server import DEFAULT_PORT


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
    KREPL_PORT: int = DEFAULT_PORT
    KREPL_LOGLEVEL: str = 'error'

    _server: KReplProc
    client: KReplClient

    def setUp(self) -> None:
        args: List[str] = []
        args += ['--port', str(self.KREPL_PORT)]
        args += ['--loglevel', self.KREPL_LOGLEVEL]

        self._server = KReplProc(*args)
        self._wait_for_port()
        self.client = KReplClient(self.KREPL_PORT)

    def tearDown(self) -> None:
        self._server.close()

    def _wait_for_port(self) -> None:
        while not self._port_is_open():
            time.sleep(0.1)

    def _port_is_open(self) -> bool:
        sock = socket(AF_INET, SOCK_STREAM)
        try:
            sock.connect(('localhost', self.KREPL_PORT))
        except BaseException:
            return False
        else:
            return True
        finally:
            sock.close()
