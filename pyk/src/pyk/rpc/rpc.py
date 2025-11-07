from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from collections.abc import Iterator
from dataclasses import dataclass
from functools import partial
from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import TYPE_CHECKING, NamedTuple

from typing_extensions import Protocol

from ..cli.cli import Options

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path
    from typing import Any, Final


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


class JsonRpcRequest(NamedTuple):
    id: str | int
    method: str
    params: Any


class JsonRpcBatchRequest(NamedTuple):
    requests: tuple[JsonRpcRequest]


class JsonRpcResult(ABC):

    @abstractmethod
    def encode(self) -> Iterator[bytes]: ...


@dataclass(frozen=True)
class JsonRpcError(JsonRpcResult):

    code: int
    message: str
    id: str | int | None

    def wrap_response(self) -> dict[str, Any]:
        return {
            'jsonrpc': JsonRpcServer.JSONRPC_VERSION,
            'error': {
                'code': self.code,
                'message': self.message,
            },
            'id': self.id,
        }

    def encode(self) -> Iterator[bytes]:
        yield json.dumps(self.wrap_response()).encode('utf-8')


@dataclass(frozen=True)
class JsonRpcSuccess(JsonRpcResult):
    payload: Any
    id: Any

    def encode(self) -> Iterator[bytes]:
        id_encoded = json.dumps(self.id)
        version_encoded = json.dumps(JsonRpcServer.JSONRPC_VERSION)
        yield f'{{"jsonrpc": {version_encoded}, "id": {id_encoded}, "result": '.encode()
        if isinstance(self.payload, Iterator):
            yield from self.payload
        else:
            yield json.dumps(self.payload).encode('utf-8')
        yield b'}'


@dataclass(frozen=True)
class JsonRpcBatchResult(JsonRpcResult):
    results: tuple[JsonRpcError | JsonRpcSuccess, ...]

    def encode(self) -> Iterator[bytes]:
        yield b'['
        first = True
        for result in self.results:
            if not first:
                yield b','
            else:
                first = False
            yield from result.encode()
        yield b']'


class JsonRpcRequestHandler(BaseHTTPRequestHandler):
    methods: dict[str, JsonRpcMethod]

    def __init__(self, methods: dict[str, JsonRpcMethod], *args: Any, **kwargs: Any) -> None:
        self.methods = methods
        super().__init__(*args, **kwargs)

    def _send_response(self, response: JsonRpcResult) -> None:
        self.send_response_headers()
        response_body = response.encode()
        for chunk in response_body:
            self.wfile.write(chunk)
        self.wfile.flush()

    def send_response_headers(self) -> None:
        self.send_response(200)
        self.send_header('Content-type', 'text/html')
        self.end_headers()

    def do_POST(self) -> None:  # noqa: N802
        content_len = self.headers.get('Content-Length')
        assert type(content_len) is str

        content = self.rfile.read(int(content_len))
        _LOGGER.debug(f'Received bytes: {content.decode()}')

        request: dict[str, Any] | list[dict[str, Any]]
        try:
            request = json.loads(content)
            _LOGGER.info(f'Received request: {request}')
        except json.JSONDecodeError:
            _LOGGER.warning(f'Invalid JSON: {content.decode()}')
            json_error = JsonRpcError(-32700, 'Invalid JSON', None)
            self._send_response(json_error)
            return

        response: JsonRpcResult
        if isinstance(request, list):
            response = self._batch_request(request)
        else:
            response = self._single_request(request)

        self._send_response(response)

    def _batch_request(self, requests: list[dict[str, Any]]) -> JsonRpcBatchResult:
        return JsonRpcBatchResult(tuple(self._single_request(request) for request in requests))

    def _single_request(self, request: dict[str, Any]) -> JsonRpcError | JsonRpcSuccess:
        validation_result = self._validate_request(request)
        if isinstance(validation_result, JsonRpcError):
            return validation_result

        id, method_name, params = validation_result
        method = self.methods[method_name]
        _LOGGER.info(f'Executing method {method_name}')
        result: Any
        if type(params) is dict:
            result = method(**params)
        elif type(params) is list:
            result = method(*params)
        elif params is None:
            result = method()
        else:
            return JsonRpcError(-32602, 'Unrecognized method parameter format.', id)
        _LOGGER.debug(f'Got response {result}')
        return JsonRpcSuccess(result, id)

    def _validate_request(self, request_dict: Any) -> JsonRpcRequest | JsonRpcError:
        required_fields = ['jsonrpc', 'method', 'id']
        for field in required_fields:
            if field not in request_dict:
                return JsonRpcError(-32600, f'Invalid request: missing field "{field}"', request_dict.get('id', None))

        jsonrpc_version = request_dict['jsonrpc']
        if jsonrpc_version != JsonRpcServer.JSONRPC_VERSION:
            return JsonRpcError(
                -32600, f'Invalid request: bad version: "{jsonrpc_version}"', request_dict.get('id', None)
            )

        method_name = request_dict['method']
        if method_name not in self.methods.keys():
            return JsonRpcError(-32601, f'Method "{method_name}" not found.', request_dict.get('id', None))

        return JsonRpcRequest(
            method=request_dict['method'], params=request_dict.get('params', None), id=request_dict.get('id', None)
        )
