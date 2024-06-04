from __future__ import annotations

import json
import logging
from functools import partial
from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import TYPE_CHECKING, Any, Final

from typing_extensions import Protocol

from ..cli.cli import Options

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path


_LOGGER: Final = logging.getLogger(__name__)


class ServeRpcOptions(Options):
    addr: str
    port: int
    definition_dir: Path | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'addr': 'localhost',
            'port': 56601,
            'definition_dir': None,
        }


class JsonRpcServer:
    JSONRPC_VERSION: Final[str] = '2.0'

    methods: dict[str, Callable[..., Any]]
    options: ServeRpcOptions
    http_server: HTTPServer | None

    def __init__(self, options: ServeRpcOptions) -> None:
        self.methods = {}
        self.options = options
        self.http_server = None

    def register_method(self, name: str, function: Callable[..., Any]) -> None:
        _LOGGER.info(f'Registered method {name} using {function}')
        self.methods[name] = function

    def serve(self) -> None:
        handler = partial(JsonRpcRequestHandler, self.methods)
        _LOGGER.info(f'Starting JSON-RPC server at {self.options.addr}:{self.options.port}')
        self.http_server = HTTPServer((self.options.addr, self.options.port), handler)
        self.http_server.serve_forever()
        _LOGGER.info(f'JSON-RPC server at {self.options.addr}:{self.options.port} shut down.')

    def shutdown(self) -> None:
        self._http_server().shutdown()

    def port(self) -> int:
        return self._http_server().server_port

    def _http_server(self) -> HTTPServer:
        if not self.http_server:
            raise ValueError('Server has not been started')
        return self.http_server


class JsonRpcMethod(Protocol):
    def __call__(self, **kwargs: Any) -> Any: ...


class JsonRpcRequestHandler(BaseHTTPRequestHandler):
    methods: dict[str, JsonRpcMethod]

    def __init__(self, methods: dict[str, JsonRpcMethod], *args: Any, **kwargs: Any) -> None:
        self.methods = methods
        super().__init__(*args, **kwargs)

    def send_json_error(self, code: int, message: str, id: Any = None) -> None:
        error_dict = {
            'jsonrpc': JsonRpcServer.JSONRPC_VERSION,
            'error': {
                'code': code,
                'message': message,
            },
            'id': id,
        }
        error_bytes = json.dumps(error_dict).encode('ascii')
        self.set_response()
        self.wfile.write(error_bytes)

    def send_json_success(self, result: Any, id: Any) -> None:
        response_dict = {
            'jsonrpc': JsonRpcServer.JSONRPC_VERSION,
            'result': result,
            'id': id,
        }
        response_bytes = json.dumps(response_dict).encode('ascii')
        self.set_response()
        self.wfile.write(response_bytes)

    def set_response(self) -> None:
        self.send_response(200)
        self.send_header('Content-type', 'text/html')
        self.end_headers()

    def do_POST(self) -> None:  # noqa: N802
        content_len = self.headers.get('Content-Length')
        assert type(content_len) is str

        content = self.rfile.read(int(content_len))
        _LOGGER.debug(f'Received bytes: {content.decode()}')

        request: dict
        try:
            request = json.loads(content)
            _LOGGER.info(f'Received request: {request}')
        except json.JSONDecodeError:
            _LOGGER.warning(f'Invalid JSON: {content.decode()}')
            self.send_json_error(-32700, 'Invalid JSON')
            return

        required_fields = ['jsonrpc', 'method', 'id']
        for field in required_fields:
            if field not in request:
                _LOGGER.warning(f'Missing required field "{field}": {request}')
                self.send_json_error(-32600, f'Invalid request: missing field "{field}"', request.get('id', None))
                return

        jsonrpc_version = request['jsonrpc']
        if jsonrpc_version != JsonRpcServer.JSONRPC_VERSION:
            _LOGGER.warning(f'Bad JSON-RPC version: {jsonrpc_version}')
            self.send_json_error(-32600, f'Invalid request: bad version: "{jsonrpc_version}"', request['id'])
            return

        method_name = request['method']
        if method_name not in self.methods:
            _LOGGER.warning(f'Method not found: {method_name}')
            self.send_json_error(-32601, f'Method "{method_name}" not found.', request['id'])
            return

        method = self.methods[method_name]
        params = request.get('params', None)
        _LOGGER.info(f'Executing method {method_name}')
        if type(params) is dict:
            result = method(**params)
        elif type(params) is list:
            result = method(*params)
        elif params is None:
            result = method()
        else:
            self.send_json_error(-32602, 'Unrecognized method parameter format.')
        _LOGGER.debug(f'Got response {result}')
        self.send_json_success(result, request['id'])
