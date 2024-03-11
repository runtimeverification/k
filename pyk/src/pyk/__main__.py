from __future__ import annotations

import logging
import sys
from typing import TYPE_CHECKING

from .cli.args import LoggingOptions
from .cli.cli import CLI
from .cli.pyk import (
    CoverageCommand,
    GraphImportsCommand,
    JsonToKoreCommand,
    KoreToJsonCommand,
    PrintCommand,
    ProveLegacyCommand,
    RPCKastCommand,
    RPCPrintCommand,
)
from .cli.utils import LOG_FORMAT, loglevel

if TYPE_CHECKING:
    from typing import Final


_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10**7)

    cli = CLI(
        [
            CoverageCommand,
            GraphImportsCommand,
            JsonToKoreCommand,
            KoreToJsonCommand,
            PrintCommand,
            ProveLegacyCommand,
            RPCKastCommand,
            RPCPrintCommand,
        ]
    )
    command = cli.get_command()
    assert isinstance(command, LoggingOptions)
    logging.basicConfig(level=loglevel(command), format=LOG_FORMAT)
    command.exec()


if __name__ == '__main__':
    main()
