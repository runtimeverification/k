import logging
from argparse import ArgumentParser
from pathlib import Path
from typing import Dict, Final

import coloredlogs

from pyk.kast.outer import read_kast_definition
from pyk.kore_exec_covr.kore_exec_covr import HaskellLogEntry, build_rule_dict, parse_rule_applications

from ..cli_utils import dir_path, file_path

_LOG_FORMAT: Final = '%(levelname)s %(name)s - %(message)s'


def do_analyze(definition_dir: Path, input_file: Path) -> None:
    """
    Inputs:
       * definition compiled with "kompile --backend haskell --emit-json"
       * Log file produced with "KORE_EXEC_OPTS='--log-format oneline --log-entries DebugAppliedRewriteRules,DebugApplyEquation'"

    Outputs:
       * human-readable report of applied rewrite and simplification rules,
         with labels (if declared) and locations
    """
    definition = read_kast_definition(definition_dir / 'compiled.json')

    print(f'Discovering rewrite and simplification rules in {definition_dir}')
    rule_dict = build_rule_dict(definition)

    defined_rewrites: Dict[str, int] = {
        key: 0 for key, rule in rule_dict.items() if not 'simplification' in rule.att.atts
    }
    defined_simplifications: Dict[str, int] = {
        key: 0 for key, rule in rule_dict.items() if 'simplification' in rule.att.atts
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
        if location_str in rule_dict and 'label' in rule_dict[location_str].att.atts:
            rule_label_str = f'[{rule_dict[location_str].att.atts["label"]}]'
        if hits > 0:
            print(f'    {hits} applications of rule {rule_label_str} defined at {location_str}')
    total_rewrites = sum([v for v in applied_rewrites.values() if v > 0])
    print(f'Total rewrites applied: {total_rewrites}')

    print('=================================')
    print('=== SIMPLIFICATIONS =============')
    print('=================================')
    for location_str, hits in applied_simplifications.items():
        rule_label_str = ''
        if location_str in rule_dict and 'label' in rule_dict[location_str].att.atts:
            rule_label_str = f'[{rule_dict[location_str].att.atts["label"]}]'
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
