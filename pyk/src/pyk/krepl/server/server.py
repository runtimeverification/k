from typing import Any, Final

from flask import Flask
from graphql_server.flask.graphqlview import GraphQLView

from .schema import SCHEMA

DEFAULT_PORT: Final = 42412


class WebServer:
    _app: Flask
    _host: str
    _port: int

    def __init__(self, host: str, port: int):
        self._host = host
        self._port = port
        self._app = Flask(__name__)

    def run(self) -> None:
        self._app.run(host=self._host, port=self._port)

    def register(self, rule: str, view_func: Any) -> None:
        self._app.add_url_rule(rule, view_func=view_func)


class KReplServer:
    _server: WebServer

    def __init__(self, host: str, port: int):
        server = WebServer(host, port)
        server.register('/', GraphQLView.as_view('graphql', schema=SCHEMA, graphiql=True))
        self._server = server

    def run(self) -> None:
        self._server.run()
