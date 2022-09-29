import logging
import sys
from argparse import ArgumentParser, FileType
from pathlib import Path
from typing import Final

from graphviz import Digraph

from .coverage import get_rule_by_id, strip_coverage_logger
from .cterm import split_config_and_constraints
from .kast import KInner, read_kast_definition
from .kastManip import flatten_label, minimize_rule, minimize_term, propagate_up_constraints, remove_source_map
from .kore.parser import KoreParser
from .kore.syntax import Pattern
from .ktool import KPrint, KProve
from .ktool.kprint import build_symbol_table, pretty_print_kast
from .prelude.k import GENERATED_TOP_CELL
from .prelude.ml import is_top, mlAnd, mlOr

_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10**7)

    cli_parser = create_argument_parser()
    args = vars(cli_parser.parse_args())

    if not args['verbose']:
        logging.basicConfig(level=logging.WARNING, format=_LOG_FORMAT)
    elif args['verbose'] == 1:
        logging.basicConfig(level=logging.INFO, format=_LOG_FORMAT)
    elif args['verbose'] > 1:
        logging.basicConfig(level=logging.DEBUG, format=_LOG_FORMAT)

    if args['command'] == 'print':
        kompiled_dir = Path(args['definition'])
        printer = KPrint(kompiled_dir, profile=args['profile'])
        _LOGGER.info(f'Reading Kast from file: {args["term"].name}')
        term = KInner.from_json(args['term'].read())
        if is_top(term):
            args['output_file'].write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {args["output_file"].name}')
        else:
            if args['minimize']:
                abstract_labels = [] if args['omit_labels'] is None else args['omit_labels'].split(',')
                minimized_disjuncts = []
                for disjunct in flatten_label('#Or', term):
                    minimized = minimize_term(disjunct, abstract_labels=abstract_labels)
                    config, constraint = split_config_and_constraints(minimized)
                    if not is_top(constraint):
                        minimized_disjuncts.append(mlAnd([config, constraint], sort=GENERATED_TOP_CELL))
                    else:
                        minimized_disjuncts.append(config)
                term = propagate_up_constraints(mlOr(minimized_disjuncts, sort=GENERATED_TOP_CELL))
            args['output_file'].write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {args["output_file"].name}')

    elif args['command'] == 'prove':
        kompiled_dir = Path(args['definition'])
        kprover = KProve(kompiled_dir, args['main-file'], profile=args['profile'])
        final_state = kprover.prove(Path(args['spec-file']), spec_module_name=args['spec-module'], args=args['kArgs'])
        args['output_file'].write(final_state.to_json())
        _LOGGER.info(f'Wrote file: {args["output_file"].name}')

    elif args['command'] == 'graph-imports':
        kompiled_dir = Path(args['definition'])
        kprinter = KPrint(kompiled_dir, profile=args['profile'])
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

    elif args['command'] == 'coverage':
        kompiled_dir = Path(args['definition'])
        json_definition = remove_source_map(read_kast_definition(kompiled_dir / 'compiled.json'))
        symbol_table = build_symbol_table(json_definition)
        for rid in args['coverage-file']:
            rule = minimize_rule(strip_coverage_logger(get_rule_by_id(json_definition, rid.strip())))
            args['output'].write('\n\n')
            args['output'].write('Rule: ' + rid.strip())
            args['output'].write('\nUnparsed:\n')
            args['output'].write(pretty_print_kast(rule, symbol_table))
        _LOGGER.info(f'Wrote file: {args["output"].name}')

    elif args['command'] == 'kore-to-json':
        kore_to_json()

    elif args['command'] == 'json-to-kore':
        json_to_kore()

    else:
        raise ValueError(f'Unknown command: {args["command"]}')


def kore_to_json() -> None:
    text = sys.stdin.read()
    kore = KoreParser(text).pattern()
    print(kore.json)


def json_to_kore() -> None:
    text = sys.stdin.read()
    kore = Pattern.from_json(text)
    print(kore.text)


def create_argument_parser() -> ArgumentParser:

    logging_args = ArgumentParser(add_help=False)
    logging_args.add_argument(
        '-v', '--verbose', action='count', help='Verbosity level, repeat for more verbosity (up to two times).'
    )
    logging_args.add_argument(
        '--profile', dest='profile', default=False, action='store_true', help='Enable coarse-grained process profiling.'
    )

    definition_args = ArgumentParser(add_help=False)
    definition_args.add_argument('definition', type=str, help='Kompiled directory for definition.')

    pyk_args = ArgumentParser()
    pyk_args_command = pyk_args.add_subparsers(dest='command')

    print_args = pyk_args_command.add_parser(
        'print', help='Pretty print a term.', parents=[logging_args, definition_args]
    )
    print_args.add_argument('term', type=FileType('r'), help='Input term (in JSON).')
    print_args.add_argument(
        '--minimize',
        dest='minimize',
        default=True,
        action='store_true',
        help='Minimize the JSON configuration before printing.',
    )
    print_args.add_argument(
        '--no-minimize',
        dest='minimize',
        action='store_false',
        help='Do not minimize the JSON configuration before printing.',
    )
    print_args.add_argument('--omit-labels', default='', nargs='?', help='List of labels to omit from output.')
    print_args.add_argument('--output-file', type=FileType('w'), default='-')

    prove_args = pyk_args_command.add_parser(
        'prove', help='Prove an input specification (using kprovex).', parents=[logging_args, definition_args]
    )
    prove_args.add_argument('main-file', type=str, help='Main file used for kompilation.')
    prove_args.add_argument('spec-file', type=str, help='File with the specification module.')
    prove_args.add_argument('spec-module', type=str, help='Module with claims to be proven.')
    prove_args.add_argument('--output-file', type=FileType('w'), default='-')
    prove_args.add_argument('kArgs', nargs='*', help='Arguments to pass through to K invocation.')

    pyk_args_command.add_parser(
        'graph-imports', help='Graph the imports of a given definition.', parents=[logging_args, definition_args]
    )

    coverage_args = pyk_args_command.add_parser(
        'coverage', help='Convert coverage file to human readable log.', parents=[logging_args, definition_args]
    )
    coverage_args.add_argument('coverage-file', type=FileType('r'), help='Coverage file to build log for.')
    coverage_args.add_argument('-o', '--output', type=FileType('w'), default='-')

    pyk_args_command.add_parser('kore-to-json', help='Convert textual KORE to JSON', parents=[logging_args])

    pyk_args_command.add_parser('json-to-kore', help='Convert JSON to textual KORE', parents=[logging_args])

    return pyk_args


if __name__ == '__main__':
    main()
