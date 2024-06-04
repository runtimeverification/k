import sys
from argparse import ArgumentParser, BooleanOptionalAction
from pathlib import Path
from typing import Any

from ..cli.utils import check_dir_path, dir_path
from .config import DIST_DIR_NAME, PROJECT_FILE_NAME
from .kbuild import KBuild
from .project import Project
from .utils import find_file_upwards


def main() -> None:
    args = vars(_argument_parser().parse_args())
    command = args['command']

    if command == 'kompile':
        return do_kompile(**args)

    if command == 'which':
        return do_which(**args)

    raise AssertionError()


def _argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Dependency management for the K Framework')
    parser.add_argument(
        '-C', '--directory', dest='start_dir', metavar='DIR', type=dir_path, default=Path('.'), help='run from DIR'
    )

    command_parser = parser.add_subparsers(dest='command', metavar='COMMAND', required=True)

    kompile_parser = command_parser.add_parser('kompile', help='kompile target')
    kompile_parser.add_argument('target_name', metavar='TARGET', help='target to build')
    kompile_parser.add_argument(
        '-o',
        '--output',
        dest='output_dir',
        metavar='OUTPUT',
        type=Path,
        help='output directory',
    )
    kompile_parser.add_argument(
        '--debug',
        action=BooleanOptionalAction,
        default=False,
        help='whether to send --debug to kompile',
    )

    which_parser = command_parser.add_parser('which', help='print definition directory for target')
    which_parser.add_argument('target_name', metavar='TARGET', help='target to print definition directory for')
    which_parser.add_argument(
        '-o',
        '--output',
        dest='output_dir',
        metavar='OUTPUT',
        type=Path,
        help='output directory',
    )

    return parser


def _project_file(start_dir: Path) -> Path:
    return find_file_upwards(PROJECT_FILE_NAME, start_dir)


def do_kompile(start_dir: Path, target_name: str, output_dir: Path | None, debug: bool, **kwargs: Any) -> None:
    project_file = _project_file(start_dir)
    project = Project.load(project_file)
    kdist_dir = output_dir or project_file.parent / DIST_DIR_NAME
    kbuild = KBuild(kdist_dir)

    definition_dir = kbuild.kompile(project, target_name, debug=debug)
    print(definition_dir)


def do_which(start_dir: Path, target_name: str, output_dir: Path | None, **kwargs: Any) -> None:
    project_file = _project_file(start_dir)
    project = Project.load(project_file)
    kdist_dir = output_dir or project_file.parent / DIST_DIR_NAME
    kbuild = KBuild(kdist_dir)

    definition_dir = kbuild.definition_dir(project, target_name)
    try:
        check_dir_path(definition_dir)
    except ValueError as e:
        print(e, file=sys.stderr)
        sys.exit(1)

    print(definition_dir)


if __name__ == '__main__':
    main()
