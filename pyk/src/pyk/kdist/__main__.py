from __future__ import annotations

import fnmatch
import logging
from typing import TYPE_CHECKING, Any

from pyk.cli.args import LoggingOptions
from pyk.cli.cli import CLI, Command
from pyk.cli.utils import loglevel

from ..kdist import kdist, target_ids

if TYPE_CHECKING:
    from argparse import ArgumentParser
    from typing import Final


_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


def main() -> None:
    kdist_cli = CLI(
        {KDistBuildCommand, KDistCleanCommand, KDistWhichCommand, KDistListCommand}, top_level_args=[LoggingOptions]
    )
    cmd = kdist_cli.get_command()
    assert isinstance(cmd, LoggingOptions)
    print(vars(cmd))
    logging.basicConfig(level=loglevel(cmd), format=_LOG_FORMAT)
    cmd.exec()


def _process_targets(targets: list[str]) -> list[str]:
    all_target_fqns = [target_id.full_name for target_id in target_ids()]
    res = []
    for pattern in targets:
        matches = fnmatch.filter(all_target_fqns, pattern)
        if not matches:
            raise ValueError(f'No target matches pattern: {pattern!r}')
        res += matches
    return res


def _process_args(args: list[str]) -> dict[str, str]:
    res: dict[str, str] = {}
    for arg in args:
        segments = arg.split('=')
        if len(segments) < 2:
            raise ValueError(f"Expected assignment of the form 'arg=value', got: {arg!r}")
        key, *values = segments
        res[key] = '='.join(values)
    return res


class KDistBuildCommand(Command, LoggingOptions):
    targets: list[str]
    force: bool
    jobs: int
    args: list[str]

    @staticmethod
    def name() -> str:
        return 'build'

    @staticmethod
    def help_str() -> str:
        return 'build targets'

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'force': False,
            'jobs': 1,
            'targets': ['*'],
            'args': [],
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('targets', metavar='TARGET', nargs='*', help='target to build')
        parser.add_argument(
            '-a',
            '--arg',
            dest='args',
            metavar='ARG',
            action='append',
            help='build with argument',
        )
        parser.add_argument('-f', '--force', default=None, action='store_true', help='force build')
        parser.add_argument('-j', '--jobs', metavar='N', type=int, help='maximal number of build jobs')

    def exec(self) -> None:
        print(self.verbose)
        print(self.debug)
        kdist.build(
            target_ids=_process_targets(self.targets),
            args=_process_args(self.args),
            jobs=self.jobs,
            force=self.force,
            verbose=self.verbose or self.debug,
        )


class KDistCleanCommand(Command, LoggingOptions):
    target: str

    @staticmethod
    def name() -> str:
        return 'clean'

    @staticmethod
    def help_str() -> str:
        return 'clean targets'

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'target': None,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            'target',
            metavar='TARGET',
            nargs='?',
            help='target to clean',
        )

    def exec(self) -> None:
        res = kdist.clean(self.target)
        print(res)


class KDistWhichCommand(Command, LoggingOptions):
    target: str

    @staticmethod
    def name() -> str:
        return 'which'

    @staticmethod
    def help_str() -> str:
        return 'print target location'

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'target': None,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            'target',
            metavar='TARGET',
            nargs='?',
            help='target to print directory for',
        )

    def exec(self) -> None:
        res = kdist.which(self.target)
        print(res)


class KDistListCommand(Command, LoggingOptions):
    @staticmethod
    def name() -> str:
        return 'list'

    @staticmethod
    def help_str() -> str:
        return 'print list of available targets'

    def exec(self) -> None:
        targets_by_plugin: dict[str, list[str]] = {}
        for plugin_name, target_name in target_ids():
            targets = targets_by_plugin.get(plugin_name, [])
            targets.append(target_name)
            targets_by_plugin[plugin_name] = targets

        for plugin_name in targets_by_plugin:
            print(plugin_name)
            for target_name in targets_by_plugin[plugin_name]:
                print(f'* {target_name}')


if __name__ == '__main__':
    main()
