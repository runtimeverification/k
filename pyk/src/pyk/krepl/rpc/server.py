import logging
from typing import Any, Callable, Final, Optional

import gevent
from gevent.pywsgi import WSGIServer
from gevent.queue import Queue
from tinyrpc.dispatch import RPCDispatcher
from tinyrpc.protocols.jsonrpc import JSONRPCProtocol
from tinyrpc.server.gevent import RPCServerGreenlets
from tinyrpc.transports.wsgi import WsgiServerTransport

_LOGGER: Final = logging.getLogger(__name__)


class JsonRpcServer:
    _server: RPCServerGreenlets
    _dispatcher: RPCDispatcher

    def __init__(self, port: int):
        transport = WsgiServerTransport(queue_class=Queue)
        protocol = JSONRPCProtocol()
        dispatcher = RPCDispatcher()

        self._wsgi_server = WSGIServer(('localhost', port), transport.handle)
        gevent.spawn(self._wsgi_server.serve_forever)

        server = RPCServerGreenlets(transport, protocol, dispatcher)
        server.trace = self._trace

        self._server = server
        self._dispatcher = dispatcher

    def _trace(self, direction: str, context: Any, message: str) -> None:
        _LOGGER.info('%s %s', direction, message)

    def serve_forever(self) -> None:
        self._server.serve_forever()

    def register(self, f: Callable, name: Optional[str] = None) -> None:
        self._dispatcher.add_method(f, name)
