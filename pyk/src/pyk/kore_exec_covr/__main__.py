from __future__ import annotations

import logging
from argparse import ArgumentParser
from typing import TYPE_CHECKING

import coloredlogs

from ..cli.utils import dir_path, file_path
from ..kast import Atts
from ..kast.outer import read_kast_definition
from .kore_exec_covr import HaskellLogEntry, build_rule_dict, parse_rule_applications

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final


_LOG_FORMAT: Final = '%(levelname)s %(name)s - %(message)s'


def do_analyze(definition_dir: Path, input_file: Path) -> None:
    """Analyze log file.

    Args:
        definition_dir: Definition kompiled with ``kompile --backend haskell --emit-json``.
        input_file: Log file produced with
          ``KORE_EXEC_OPTS='--log-format oneline --log-entries DebugAppliedRewriteRules,DebugApplyEquation'``.

    Returns:
        Human-readable report of applied rewrite and simplification rules,
        with labels (if declared) and locations.
    """
    definition = read_kast_definition(definition_dir / 'compiled.json')

    print(f'Discovering rewrite and simplification rules in {definition_dir}')
    rule_dict = build_rule_dict(definition)

    defined_rewrites: dict[str, int] = {
        key: 0 for key, rule in rule_dict.items() if not Atts.SIMPLIFICATION in rule.att
    }
    defined_simplifications: dict[str, int] = {
        key: 0 for key, rule in rule_dict.items() if Atts.SIMPLIFICATION in rule.att
    }
    print(f'    Found {len(defined_rewrites)} rewrite rules availible for {definition.main_module_name}')
    print(f'    Found {len(defined_simplifications)} simplification rules availible for {definition.main_module_name}')

    parsed_rule_applictions = parse_rule_applications(input_file)
    applied_rewrites = parsed_rule_applictions[HaskellLogEntry.DEBUG_APPLIED_REWRITE_RULES]
    applied_simplifications = parsed_rule_applictions[HaskellLogEntry.DEBUG_APPLY_EQUATION]

    print('=================================')
    print('=== REWRITES ====================')
    print('=================================')
    for location_str, hits in applied_rewrites.items():
        rule_label_str = ''
        if location_str in rule_dict and Atts.LABEL in rule_dict[location_str].att:
            rule_label_str = f'[{rule_dict[location_str].att[Atts.LABEL]}]'
        if hits > 0:
            print(f'    {hits} applications of rule {rule_label_str} defined at {location_str}')
    total_rewrites = sum([v for v in applied_rewrites.values() if v > 0])
    print(f'Total rewrites applied: {total_rewrites}')

    print('=================================')
    print('=== SIMPLIFICATIONS =============')
    print('=================================')
    for location_str, hits in applied_simplifications.items():
        rule_label_str = ''
        if location_str in rule_dict and Atts.KLABEL in rule_dict[location_str].att:
            rule_label_str = f'[{rule_dict[location_str].att[Atts.LABEL]}]'
        if hits > 0:
            print(f'    {hits} applications of rule {rule_label_str} defined at {location_str}')
    total_simplifications = sum([v for v in applied_simplifications.values() if v > 0])
    print(f'Total applied simplifications: {total_simplifications}')


def main() -> None:
    args = _argument_parser().parse_args()

    level = logging.ERROR if args.quiet else logging.INFO
    logging.basicConfig(level=level, format=_LOG_FORMAT)
    coloredlogs.install(level=level, fmt=_LOG_FORMAT)

    return do_analyze(definition_dir=args.definition_dir, input_file=args.input_file)


def _argument_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Symbolic execution logs analysis tool')
    parser.add_argument(
        '--definition-dir',
        type=dir_path,
        help='Path to Haskell-kompiled definition to use.',
    )
    parser.add_argument('--quiet', action='store_true', help='be quiet and do not output warnings')
    parser.add_argument('input_file', type=file_path, help='path to kore-exec log file to analyze')

    return parser


if __name__ == '__main__':
    main()
