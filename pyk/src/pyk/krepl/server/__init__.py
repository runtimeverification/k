from typing import Any, Dict, Final, List, Mapping

from flask import Response, jsonify, make_response, request

from pyk.kore.parser import KoreParser
from pyk.kore.syntax import Pattern

from ..web.server import WebServer

DEFAULT_PORT: Final = 42412


class KReplState:
    """Store proof tree and expose domain-specific methods over it. Will eventually be encapsualted in a user session."""

    def load_raw(self, pattern: Pattern) -> None:
        return

    def step_to_branch(self) -> str:
        return '1'


class KReplServer:
    _server: WebServer
    _state: KReplState

    def __init__(self, port: int):
        server = WebServer(port)
        server.register('/load-raw', self.load_raw, method='POST')
        server.register('/step-to-branch', self.step_to_branch, method='POST')
        self._server = server
        self._state = KReplState()

    def run(self) -> None:
        self._server.run()

    def load_raw(self) -> Response:
        payload = request.json
        text = (payload or {}).get('term')
        if text is None:
            return make_response('Bad request', 400)

        try:
            pattern = KoreParser(text).pattern()
        except ValueError as err:
            return make_response(err.args[0], 400)

        self._state.load_raw(pattern)
        return jsonify({'success': True})

    def step_to_branch(self) -> Response:
        config_id = self._state.step_to_branch()
        return jsonify({'configId': config_id})
