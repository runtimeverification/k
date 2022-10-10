from subprocess import Popen
from typing import Any, ContextManager, Iterable
from unittest import TestCase


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
    KREPL_ARGS: Iterable[str] = ()

    _server: KReplProc

    def setUp(self) -> None:
        self._server = KReplProc(*self.KREPL_ARGS)

    def tearDown(self) -> None:
        self._server.close()
