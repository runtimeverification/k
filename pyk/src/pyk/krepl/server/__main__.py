import logging
import signal
import time
from argparse import ArgumentParser
from typing import Any, Final

from pyk.cli_utils import loglevel

_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    args = argument_parser().parse_args()
    logging.basicConfig(level=args.loglevel, format=_LOG_FORMAT)

    _LOGGER.info('Server started')

    listener = _Listener()
    while not listener.terminated:
        time.sleep(1)

    _LOGGER.info('Server stopped')


def argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='K-REPL Server')
    parser.add_argument('-l', '--loglevel', type=loglevel, default=logging.INFO, metavar='LEVEL', help='log level')
    return parser


class _Listener:
    terminated: bool

    def __init__(self) -> None:
        self.terminated = False
        signal.signal(signal.SIGINT, self._terminate)
        signal.signal(signal.SIGTERM, self._terminate)

    def _terminate(self, *args: Any) -> None:
        self.terminated = True


if __name__ == '__main__':
    main()
