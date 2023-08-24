from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser, FileType
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from graphviz import Digraph

from .cli.args import KCLIArgs
from .cli.utils import LOG_FORMAT, dir_path, loglevel
from .coverage import get_rule_by_id, strip_coverage_logger
from .cterm import split_config_and_constraints
from .kast.inner import KInner
from .kast.manip import flatten_label, minimize_rule, minimize_term, propagate_up_constraints, remove_source_map
from .kast.outer import read_kast_definition
from .kast.pretty import PrettyPrinter
from .kore.parser import KoreParser
from .kore.syntax import Pattern
from .ktool.kprint import KPrint
from .ktool.kprove import KProve
from .prelude.k import GENERATED_TOP_CELL
from .prelude.ml import is_top, mlAnd, mlOr

if TYPE_CHECKING:
    from argparse import Namespace
    from typing import Any, Final


_LOGGER: Final = logging.getLogger(__name__)


class PrintInput(Enum):
    KORE_JSON = 'kore-json'
    KAST_JSON = 'kast-json'


def main() -> None:
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10**7)

    cli_parser = create_argument_parser()
    args = cli_parser.parse_args()

    logging.basicConfig(level=loglevel(args), format=LOG_FORMAT)

    executor_name = 'exec_' + args.command.lower().replace('-', '_')
    if executor_name not in globals():
        raise AssertionError(f'Unimplemented command: {args.command}')

    execute = globals()[executor_name]
    execute(args)


def exec_print(args: Namespace) -> None:
    kompiled_dir: Path = args.definition_dir
    printer = KPrint(kompiled_dir)
    if args.input == PrintInput.KORE_JSON:
        _LOGGER.info(f'Reading Kore JSON from file: {args.term.name}')
        kore = Pattern.from_json(args.term.read())
        term = printer.kore_to_kast(kore)
    else:
        _LOGGER.info(f'Reading Kast JSON from file: {args.term.name}')
        term = KInner.from_json(args.term.read())
    if is_top(term):
        args.output_file.write(printer.pretty_print(term))
        _LOGGER.info(f'Wrote file: {args.output_file.name}')
    else:
        if args.minimize:
            if args.omit_labels != '' and args.keep_cells != '':
                raise ValueError('You cannot use both --omit-labels and --keep-cells.')

            abstract_labels = args.omit_labels.split(',') if args.omit_labels != '' else []
            keep_cells = args.keep_cells.split(',') if args.keep_cells != '' else []
            minimized_disjuncts = []

            for disjunct in flatten_label('#Or', term):
                try:
                    minimized = minimize_term(disjunct, abstract_labels=abstract_labels, keep_cells=keep_cells)
                    config, constraint = split_config_and_constraints(minimized)
                except ValueError as err:
                    raise ValueError('The minimized term does not contain a config cell.') from err

                if not is_top(constraint):
                    minimized_disjuncts.append(mlAnd([config, constraint], sort=GENERATED_TOP_CELL))
                else:
                    minimized_disjuncts.append(config)
            term = propagate_up_constraints(mlOr(minimized_disjuncts, sort=GENERATED_TOP_CELL))

        args.output_file.write(printer.pretty_print(term))
        _LOGGER.info(f'Wrote file: {args.output_file.name}')


def exec_prove(args: Namespace) -> None:
    kompiled_dir: Path = args.definition_dir
    kprover = KProve(kompiled_dir, args.main_file)
    final_state = kprover.prove(Path(args.spec_file), spec_module_name=args.spec_module, args=args.kArgs)
    args.output_file.write(json.dumps(mlOr([state.kast for state in final_state]).to_dict()))
    _LOGGER.info(f'Wrote file: {args.output_file.name}')


def exec_graph_imports(args: Namespace) -> None:
    kompiled_dir: Path = args.definition_dir
    kprinter = KPrint(kompiled_dir)
    definition = kprinter.definition
    import_graph = Digraph()
    graph_file = kompiled_dir / 'import-graph'
    for module in definition.modules:
        module_name = module.name
        import_graph.node(module_name)
        for module_import in module.imports:
            import_graph.edge(module_name, module_import.name)
    import_graph.render(graph_file)
    _LOGGER.info(f'Wrote file: {graph_file}')


def exec_coverage(args: Namespace) -> None:
    kompiled_dir: Path = args.definition_dir
    definition = remove_source_map(read_kast_definition(kompiled_dir / 'compiled.json'))
    pretty_printer = PrettyPrinter(definition)
    for rid in args.coverage_file:
        rule = minimize_rule(strip_coverage_logger(get_rule_by_id(definition, rid.strip())))
        args.output.write('\n\n')
        args.output.write('Rule: ' + rid.strip())
        args.output.write('\nUnparsed:\n')
        args.output.write(pretty_printer.print(rule))
    _LOGGER.info(f'Wrote file: {args.output.name}')


def exec_kore_to_json(args: Namespace) -> None:
    text = sys.stdin.read()
    kore = KoreParser(text).pattern()
    print(kore.json)


def exec_json_to_kore(args: dict[str, Any]) -> None:
    text = sys.stdin.read()
    kore = Pattern.from_json(text)
    kore.write(sys.stdout)
    sys.stdout.write('\n')


def create_argument_parser() -> ArgumentParser:
    k_cli_args = KCLIArgs()

    definition_args = ArgumentParser(add_help=False)
    definition_args.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')

    pyk_args = ArgumentParser()
    pyk_args_command = pyk_args.add_subparsers(dest='command', required=True)

    print_args = pyk_args_command.add_parser(
        'print',
        help='Pretty print a term.',
        parents=[k_cli_args.logging_args, definition_args, k_cli_args.display_args],
    )
    print_args.add_argument('term', type=FileType('r'), help='Input term (in format specified with --input).')
    print_args.add_argument('--input', default=PrintInput.KAST_JSON, type=PrintInput, choices=list(PrintInput))
    print_args.add_argument('--omit-labels', default='', nargs='?', help='List of labels to omit from output.')
    print_args.add_argument(
        '--keep-cells', default='', nargs='?', help='List of cells with primitive values to keep in output.'
    )
    print_args.add_argument('--output-file', type=FileType('w'), default='-')

    prove_args = pyk_args_command.add_parser(
        'prove',
        help='Prove an input specification (using kprovex).',
        parents=[k_cli_args.logging_args, definition_args],
    )
    prove_args.add_argument('main_file', type=str, help='Main file used for kompilation.')
    prove_args.add_argument('spec_file', type=str, help='File with the specification module.')
    prove_args.add_argument('spec_module', type=str, help='Module with claims to be proven.')
    prove_args.add_argument('--output-file', type=FileType('w'), default='-')
    prove_args.add_argument('kArgs', nargs='*', help='Arguments to pass through to K invocation.')

    pyk_args_command.add_parser(
        'graph-imports',
        help='Graph the imports of a given definition.',
        parents=[k_cli_args.logging_args, definition_args],
    )

    coverage_args = pyk_args_command.add_parser(
        'coverage',
        help='Convert coverage file to human readable log.',
        parents=[k_cli_args.logging_args, definition_args],
    )
    coverage_args.add_argument('coverage_file', type=FileType('r'), help='Coverage file to build log for.')
    coverage_args.add_argument('-o', '--output', type=FileType('w'), default='-')

    pyk_args_command.add_parser('kore-to-json', help='Convert textual KORE to JSON', parents=[k_cli_args.logging_args])

    pyk_args_command.add_parser('json-to-kore', help='Convert JSON to textual KORE', parents=[k_cli_args.logging_args])

    return pyk_args


if __name__ == '__main__':
    main()
