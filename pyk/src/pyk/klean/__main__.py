from __future__ import annotations

from argparse import ArgumentParser
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli.utils import dir_path
from ..kore.internal import KoreDefn

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Iterable


@dataclass(frozen=True)
class CliError(Exception):
    message: str
    status: int


def main() -> None:
    import logging
    import sys

    from ..cli.utils import LOG_FORMAT

    args = sys.argv
    level, args = _extract_log_level(args)
    logging.basicConfig(level=level, format=LOG_FORMAT)

    try:
        klean(args)
    except CliError as err:
        match err:
            case CliError(message, status):
                print(f'Error: {message}', file=sys.stderr)
                raise SystemExit(status) from err
            case _:
                raise AssertionError() from None


def _extract_log_level(args: list[str]) -> tuple[int, list[str]]:
    from ..cli.args import KCLIArgs
    from ..cli.utils import loglevel

    parser = KCLIArgs().logging_args
    ns, rest = parser.parse_known_args(args)
    level = loglevel(ns)
    return level, rest


def klean(args: Iterable[str]) -> None:
    from .generate import generate

    ns = _parse_args(args)
    output_dir = ns.output_dir or Path()
    package_dir = output_dir / ns.package_name
    if package_dir.exists():
        raise CliError(f'Directory exists: {package_dir}', 115)

    defn = _load_defn(ns.definition_dir)
    if ns.rules:
        defn = defn.filter_rewrites(ns.rules)
    defn = defn.project_to_rewrites()
    generate(
        defn=defn,
        output_dir=output_dir,
        context={
            'package_name': ns.package_name,
            'library_name': ns.library_name,
        },
        config={
            'derive_beq': ns.derive_beq,
            'derive_decidableeq': ns.derive_decidableeq,
        },
    )


def _parse_args(args: Iterable[str]) -> Namespace:
    parser = _parser()
    args = list(args)[1:]
    ns = parser.parse_args(args)

    if ns.library_name is None:
        ns.library_name = ''.join(word.capitalize() for word in ns.package_name.split('-'))

    if ns.output_dir is None:
        ns.output_dir = Path()

    return ns


def _parser() -> ArgumentParser:
    parser = ArgumentParser(description='Generate a Lean 4 project from a K definition')
    parser.add_argument('definition_dir', metavar='DEFN_DIR', type=dir_path, help='definition directory')
    parser.add_argument('package_name', metavar='PKG_NAME', help='name of the generated Lean 4 package (in kebab-case)')
    parser.add_argument(
        '-o',
        '--output',
        dest='output_dir',
        metavar='DIR',
        type=dir_path,
        help='output directory (default: .)',
    )
    parser.add_argument(
        '-l',
        '--library',
        dest='library_name',
        metavar='NAME',
        help='name of the generated Lean library (default: package name in PascalCase)',
    )
    parser.add_argument(
        '-r',
        '--rule',
        dest='rules',
        metavar='LABEL',
        action='append',
        help='labels of rules to include (default: all)',
    )
    parser.add_argument(
        '--derive-beq',
        action='store_true',
        help='derive BEq for all types',
    )
    parser.add_argument(
        '--derive-decidableeq',
        action='store_true',
        help='derive DecidableEq for all types except SortKItem and its dependents',
    )
    return parser


def _load_defn(definition_dir: Path) -> KoreDefn:
    from ..kore.parser import KoreParser

    kore_text = (definition_dir / 'definition.kore').read_text()
    definition = KoreParser(kore_text).definition()
    return KoreDefn.from_definition(definition)


if __name__ == '__main__':
    main()
