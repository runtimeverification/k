from typing import Any, Callable, Optional

from tinyrpc import RPCClient
from tinyrpc.protocols.jsonrpc import JSONRPCProtocol
from tinyrpc.transports.http import HttpPostClientTransport


class JsonRpcClient:
    def __init__(self, port: int, *, timeout: Optional[float] = None):
        protocol = JSONRPCProtocol()
        transport = HttpPostClientTransport(f'http://localhost:{port}', timeout=timeout)
        client = RPCClient(protocol, transport)

        self._client = client

    def __getattr__(self, name: str) -> Callable:
        def method(*args: Any, **kwargs: Any) -> Any:
            return self._client.call(name, args=args, kwargs=kwargs)

        return method
