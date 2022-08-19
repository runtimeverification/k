import argparse
import logging
import sys
from pathlib import Path
from typing import Final

from graphviz import Digraph

from .coverage import getRuleById, stripCoverageLogger
from .cterm import split_config_and_constraints
from .kast import KAst, flatten_label, read_kast_definition
from .kastManip import minimize_rule, minimize_term, propagate_up_constraints, removeSourceMap
from .ktool import KPrint, KProve
from .ktool.kprint import build_symbol_table, pretty_print_kast
from .prelude import Sorts, mlAnd, mlOr, mlTop

_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'
_LOGGER: Final = logging.getLogger(__name__)


def main():
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10**7)

    cli_parser = create_argument_parser()
    args = vars(cli_parser.parse_args())

    kompiled_dir = Path(args['definition'])

    if not args['verbose']:
        logging.basicConfig(level=logging.WARNING, format=_LOG_FORMAT)
    elif args['verbose'] == 1:
        logging.basicConfig(level=logging.INFO, format=_LOG_FORMAT)
    elif args['verbose'] > 1:
        logging.basicConfig(level=logging.DEBUG, format=_LOG_FORMAT)

    if args['command'] == 'print':
        printer = KPrint(kompiled_dir, profile=args['profile'])
        _LOGGER.info(f'Reading Kast from file: {args["term"].name}')
        term = KAst.from_json(args['term'].read())
        if type(term) is dict and 'term' in term:
            term = term['term']
        if term == mlTop():
            args['output_file'].write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {args["output_file"].name}')
        else:
            if args['minimize']:
                abstractLabels = [] if args['omit_labels'] is None else args['omit_labels'].split(',')
                minimizedDisjuncts = []
                for d in flatten_label('#Or', term):
                    dMinimized = minimize_term(d, abstract_labels=abstractLabels)
                    dConfig, dConstraint = split_config_and_constraints(dMinimized)
                    if dConstraint != mlTop():
                        minimizedDisjuncts.append(mlAnd([dConfig, dConstraint], sort=Sorts.GENERATED_TOP_CELL))
                    else:
                        minimizedDisjuncts.append(dConfig)
                term = propagate_up_constraints(mlOr(minimizedDisjuncts, sort=Sorts.GENERATED_TOP_CELL))
            args['output_file'].write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {args["output_file"].name}')

    elif args['command'] == 'prove':
        kprover = KProve(kompiled_dir, args['main-file'], profile=args['profile'])
        finalState = kprover.prove(Path(args['spec-file']), spec_module_name=args['spec-module'], args=args['kArgs'])
        args['output_file'].write(finalState.to_json())
        _LOGGER.info(f'Wrote file: {args["output_file"].name}')

    elif args['command'] == 'graph-imports':
        kprinter = KPrint(kompiled_dir, profile=args['profile'])
        kDefn = kprinter.definition
        importGraph = Digraph()
        graphFile = kompiled_dir / 'import-graph'
        for module in kDefn.modules:
            modName = module.name
            importGraph.node(modName)
            for moduleImport in module.imports:
                importGraph.edge(modName, moduleImport.name)
        importGraph.render(graphFile)
        _LOGGER.info(f'Wrote file: {graphFile}')

    elif args['command'] == 'coverage':
        json_definition = removeSourceMap(read_kast_definition(kompiled_dir / 'compiled.json'))
        symbol_table = build_symbol_table(json_definition)
        for rid in args['coverage-file']:
            rule = minimize_rule(stripCoverageLogger(getRuleById(json_definition, rid.strip())))
            args['output'].write('\n\n')
            args['output'].write('Rule: ' + rid.strip())
            args['output'].write('\nUnparsed:\n')
            args['output'].write(pretty_print_kast(rule, symbol_table))
        _LOGGER.info(f'Wrote file: {args["output"].name}')

    else:
        raise ValueError(f'Unknown command: {args["command"]}')


def create_argument_parser():

    logging_args = argparse.ArgumentParser(add_help=False)
    logging_args.add_argument(
        '-v', '--verbose', action='count', help='Verbosity level, repeat for more verbosity (up to two times).'
    )
    logging_args.add_argument(
        '--profile', dest='profile', default=False, action='store_true', help='Enable coarse-grained process profiling.'
    )

    definition_args = argparse.ArgumentParser(add_help=False)
    definition_args.add_argument('definition', type=str, help='Kompiled directory for definition.')

    pyk_args = argparse.ArgumentParser()
    pyk_args_command = pyk_args.add_subparsers(dest='command')

    print_args = pyk_args_command.add_parser(
        'print', help='Pretty print a term.', parents=[logging_args, definition_args]
    )
    print_args.add_argument('term', type=argparse.FileType('r'), help='Input term (in JSON).')
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
    print_args.add_argument('--output-file', type=argparse.FileType('w'), default='-')

    prove_args = pyk_args_command.add_parser(
        'prove', help='Prove an input specification (using kprovex).', parents=[logging_args, definition_args]
    )
    prove_args.add_argument('main-file', type=str, help='Main file used for kompilation.')
    prove_args.add_argument('spec-file', type=str, help='File with the specification module.')
    prove_args.add_argument('spec-module', type=str, help='Module with claims to be proven.')
    prove_args.add_argument('--output-file', type=argparse.FileType('w'), default='-')
    prove_args.add_argument('kArgs', nargs='*', help='Arguments to pass through to K invocation.')

    pyk_args_command.add_parser(
        'graph-imports', help='Graph the imports of a given definition.', parents=[logging_args, definition_args]
    )

    coverage_args = pyk_args_command.add_parser(
        'coverage', help='Convert coverage file to human readable log.', parents=[logging_args, definition_args]
    )
    coverage_args.add_argument('coverage-file', type=argparse.FileType('r'), help='Coverage file to build log for.')
    coverage_args.add_argument('-o', '--output', type=argparse.FileType('w'), default='-')

    return pyk_args


if __name__ == '__main__':
    main()
