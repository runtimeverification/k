from subprocess import Popen
from typing import Any, ContextManager


class KReplServerProc(ContextManager['KReplServerProc']):
    _proc: Popen

    def __init__(self, *args: str):
        self._proc = Popen(('krepl-server',) + args)

    def __enter__(self) -> 'KReplServerProc':
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    def close(self) -> None:
        self._proc.terminate()
        self._proc.wait()

    @property
    def pid(self) -> int:
        return self._proc.pid
