import logging
from argparse import ArgumentParser
from typing import Final

from pyk.cli_utils import loglevel

from ..rpc.server import JsonRpcServer
from . import DEFAULT_PORT

_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    args = argument_parser().parse_args()
    logging.basicConfig(level=args.loglevel, format=_LOG_FORMAT)

    server = JsonRpcServer(args.port)
    server.register(echo)

    _LOGGER.info(f'Server started at port {args.port}')
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        ...
    _LOGGER.info('Server stopped')


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Server')
    parser.add_argument('-l', '--loglevel', type=loglevel, default=logging.INFO, metavar='LEVEL', help='log level')
    parser.add_argument('-p', '--port', type=int, default=DEFAULT_PORT, help='server port')
    return parser


def echo(msg: str) -> str:
    return msg


if __name__ == '__main__':
    main()
