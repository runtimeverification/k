from typing import Any, Final, List, Mapping

DEFAULT_PORT: Final = 42412

from pyk.kore.parser import KoreParser
from pyk.kore.syntax import Pattern

from ..rpc.server import JsonRpcServer


class KReplState:
    """Store proof tree and expose domain-specific methods over it. Will eventually be encapsualted in a user session."""

    def load_raw(self, pattern: Pattern) -> None:
        return

    def step_to_branch(self) -> str:
        return ''


class KReplServer:
    _server: JsonRpcServer
    _state: KReplState

    def __init__(self, port: int):
        server = JsonRpcServer(port)
        server.register(self.load_raw)
        server.register(self.step_to_branch)
        self._server = server
        self._state = KReplState()

    def serve_forever(self) -> None:
        self._server.serve_forever()

    def load_raw(self, text: str) -> None:
        pattern = KoreParser(text).pattern()
        return self._state.load_raw(pattern)

    def step_to_branch(self) -> str:
        return self._state.step_to_branch()
