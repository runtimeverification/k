import shutil
from argparse import ArgumentParser
from pathlib import Path
from typing import Any

from ..cli_utils import dir_path
from .config import KBUILD_DIR, PROJECT_FILE_NAME
from .kbuild import KBuild
from .package import Package
from .utils import find_file_upwards


def main() -> None:
    args = vars(_argument_parser().parse_args())
    command = args['command']

    if command == 'clean':
        return do_clean(**args)

    if command == 'kompile':
        return do_kompile(**args)

    raise AssertionError()


def _argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Dependency management for the K Framework')
    parser.add_argument(
        '-C', '--directory', dest='start_dir', metavar='DIR', type=dir_path, default=Path('.'), help='run from DIR'
    )

    command_parser = parser.add_subparsers(dest='command', metavar='COMMAND', required=True)

    command_parser.add_parser('clean', help='clean build cache')

    kompile_parser = command_parser.add_parser('kompile', help='kompile target')
    kompile_parser.add_argument('target_name', metavar='TARGET', help='target to build')

    return parser


def do_clean(**kwargs: Any) -> None:
    shutil.rmtree(KBUILD_DIR, ignore_errors=True)


def do_kompile(start_dir: Path, target_name: str, **kwargs: Any) -> None:
    project_file = find_file_upwards(PROJECT_FILE_NAME, start_dir)
    package = Package.create(project_file)
    kbuild = KBuild(KBUILD_DIR)
    definition_dir = kbuild.kompile(package, target_name)
    print(definition_dir)


if __name__ == '__main__':
    main()
