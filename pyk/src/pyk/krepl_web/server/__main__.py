import logging
from argparse import ArgumentParser
from typing import Final

from pyk.cli_utils import loglevel

from . import DEFAULT_PORT, KReplServer

_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    args = argument_parser().parse_args()
    logging.basicConfig(level=args.loglevel, format=_LOG_FORMAT)

    _LOGGER.info(f'Server started at port {args.port}')
    KReplServer(args.host, args.port).run()
    _LOGGER.info('Server stopped')


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Server')
    parser.add_argument('-l', '--loglevel', type=loglevel, default=logging.INFO, metavar='LEVEL', help='log level')
    parser.add_argument('-s', '--host', type=str, default='localhost', help='server host (default: localhost)')
    parser.add_argument('-p', '--port', type=int, default=DEFAULT_PORT, help=f'server port (default: {DEFAULT_PORT})')
    return parser


if __name__ == '__main__':
    main()
