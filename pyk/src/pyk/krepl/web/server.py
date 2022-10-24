from enum import Enum
from typing import Callable, Literal

from flask import Flask


class WebServer:
    _app: Flask
    _port: int

    class _Method(Enum):
        GET = 'GET'
        POST = 'POST'

    def __init__(self, port: int):
        self._port = port
        self._app = Flask(__name__)

    def run(self) -> None:
        self._app.run(host='localhost', port=self._port)

    def register(self, rule: str, handler: Callable, *, method: Literal['GET', 'POST']) -> None:
        self._app.add_url_rule(rule, view_func=handler, methods=[self._Method(method).value])
