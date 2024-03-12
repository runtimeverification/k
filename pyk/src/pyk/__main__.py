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
from .cterm import CTerm
from .kast.inner import KInner
from .kast.manip import (
    flatten_label,
    minimize_rule,
    minimize_term,
    propagate_up_constraints,
    remove_source_map,
    split_config_and_constraints,
)
from .kast.outer import read_kast_definition
from .kast.pretty import PrettyPrinter
from .kore.parser import KoreParser
from .kore.rpc import ExecuteResult, StopReason
from .kore.syntax import Pattern, kore_term
from .ktool import TypeInferenceMode
from .ktool.kompile import Kompile, KompileBackend
from .ktool.kprint import KPrint
from .ktool.kprove import KProve
from .prelude.k import GENERATED_TOP_CELL
from .prelude.ml import is_top, mlAnd, mlOr
from .proof.reachability import APRFailureInfo
from .utils import check_file_path, ensure_dir_path

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


def exec_rpc_print(args: Namespace) -> None:
    kompiled_dir: Path = args.definition_dir
    printer = KPrint(kompiled_dir)
    input_dict = json.loads(args.input_file.read())
    output_buffer = []

    def pretty_print_request(request_params: dict[str, Any]) -> list[str]:
        output_buffer = []
        non_state_keys = set(request_params.keys()).difference(['state'])
        for key in non_state_keys:
            output_buffer.append(f'{key}: {request_params[key]}')
        state = CTerm.from_kast(printer.kore_to_kast(kore_term(request_params['state'])))
        output_buffer.append('State:')
        output_buffer.append(printer.pretty_print(state.kast, sort_collections=True))
        return output_buffer

    def pretty_print_execute_response(execute_result: ExecuteResult) -> list[str]:
        output_buffer = []
        output_buffer.append(f'Depth: {execute_result.depth}')
        output_buffer.append(f'Stop reason: {execute_result.reason.value}')
        if execute_result.reason == StopReason.TERMINAL_RULE or execute_result.reason == StopReason.CUT_POINT_RULE:
            output_buffer.append(f'Stop rule: {execute_result.rule}')
        output_buffer.append(
            f'Number of next states: {len(execute_result.next_states) if execute_result.next_states is not None else 0}'
        )
        state = CTerm.from_kast(printer.kore_to_kast(execute_result.state.kore))
        output_buffer.append('State:')
        output_buffer.append(printer.pretty_print(state.kast, sort_collections=True))
        if execute_result.next_states is not None:
            next_states = [CTerm.from_kast(printer.kore_to_kast(s.kore)) for s in execute_result.next_states]
            for i, s in enumerate(next_states):
                output_buffer.append(f'Next state #{i}:')
                output_buffer.append(printer.pretty_print(s.kast, sort_collections=True))
        return output_buffer

    try:
        if 'method' in input_dict:
            output_buffer.append('JSON RPC request')
            output_buffer.append(f'id: {input_dict["id"]}')
            output_buffer.append(f'Method: {input_dict["method"]}')
            try:
                if 'state' in input_dict['params']:
                    output_buffer += pretty_print_request(input_dict['params'])
                else:  # this is an "add-module" request, skip trying to print state
                    for key in input_dict['params'].keys():
                        output_buffer.append(f'{key}: {input_dict["params"][key]}')
            except KeyError as e:
                _LOGGER.critical(f'Could not find key {str(e)} in input JSON file')
                exit(1)
        else:
            if not 'result' in input_dict:
                _LOGGER.critical('The input is neither a request not a resonse')
                exit(1)
            output_buffer.append('JSON RPC Response')
            output_buffer.append(f'id: {input_dict["id"]}')
            if list(input_dict['result'].keys()) == ['state']:  # this is a "simplify" response
                output_buffer.append('Method: simplify')
                state = CTerm.from_kast(printer.kore_to_kast(kore_term(input_dict['result']['state'])))
                output_buffer.append('State:')
                output_buffer.append(printer.pretty_print(state.kast, sort_collections=True))
            elif list(input_dict['result'].keys()) == ['module']:  # this is an "add-module" response
                output_buffer.append('Method: add-module')
                output_buffer.append('Module:')
                output_buffer.append(input_dict['result']['module'])
            else:
                try:  # assume it is an "execute" response
                    output_buffer.append('Method: execute')
                    execute_result = ExecuteResult.from_dict(input_dict['result'])
                    output_buffer += pretty_print_execute_response(execute_result)
                except KeyError as e:
                    _LOGGER.critical(f'Could not find key {str(e)} in input JSON file')
                    exit(1)
        if args.output_file is not None:
            args.output_file.write('\n'.join(output_buffer))
        else:
            print('\n'.join(output_buffer))
    except ValueError as e:
        # shorten and print the error message in case kore_to_kast throws ValueError
        _LOGGER.critical(str(e)[:200])
        exit(1)


def exec_rpc_kast(args: Namespace) -> None:
    """
    Convert an 'execute' JSON RPC response to a new 'execute' or 'simplify' request,
    copying parameters from a reference request.
    """
    reference_request = json.loads(args.reference_request_file.read())
    input_dict = json.loads(args.response_file.read())
    execute_result = ExecuteResult.from_dict(input_dict['result'])
    non_state_keys = set(reference_request['params'].keys()).difference(['state'])
    request_params = {}
    for key in non_state_keys:
        request_params[key] = reference_request['params'][key]
    request_params['state'] = {'format': 'KORE', 'version': 1, 'term': execute_result.state.kore.dict}
    request = {
        'jsonrpc': reference_request['jsonrpc'],
        'id': reference_request['id'],
        'method': reference_request['method'],
        'params': request_params,
    }
    args.output_file.write(json.dumps(request))


def exec_prove_legacy(args: Namespace) -> None:
    kompiled_dir: Path = args.definition_dir
    kprover = KProve(kompiled_dir, args.main_file)
    final_state = kprover.prove(Path(args.spec_file), spec_module_name=args.spec_module, args=args.kArgs)
    args.output_file.write(json.dumps(mlOr([state.kast for state in final_state]).to_dict()))
    _LOGGER.info(f'Wrote file: {args.output_file.name}')


def exec_prove(args: Namespace) -> None:
    kompiled_directory: Path
    if args.definition_dir is None:
        kompiled_directory = Kompile.default_directory()
        _LOGGER.info(f'Using kompiled directory: {kompiled_directory}.')
    else:
        kompiled_directory = args.definition_dir
    kprove = KProve(kompiled_directory)
    proofs = kprove.prove_rpc(Path(args.spec_file), args.spec_module, type_inference_mode=args.type_inference_mode)
    for proof in proofs:
        print('\n'.join(proof.summary.lines))
        if proof.failed and args.failure_info:
            failure_info = proof.failure_info
            if type(failure_info) is APRFailureInfo:
                print('\n'.join(failure_info.print()))
    sys.exit(len([p.id for p in proofs if not p.passed]))


def exec_kompile(args: Namespace) -> None:
    main_file = Path(args.main_file)
    check_file_path(main_file)
    kompiled_directory: Path
    if 'definition_dir' not in args:
        kompiled_directory = Path(f'{main_file.stem}-kompiled')
        ensure_dir_path(kompiled_directory)
    else:
        kompiled_directory = args.definition_dir
    kompile_dict = {
        'main_file': main_file,
        'backend': args.backend.value,
    }
    Kompile.from_dict(kompile_dict)(
        output_dir=kompiled_directory,
        type_inference_mode=args.type_inference_mode,
    )


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

    pyk_args = ArgumentParser()
    pyk_args_command = pyk_args.add_subparsers(dest='command', required=True)

    print_args = pyk_args_command.add_parser(
        'print',
        help='Pretty print a term.',
        parents=[k_cli_args.logging_args, k_cli_args.display_args],
    )
    print_args.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')
    print_args.add_argument('term', type=FileType('r'), help='Input term (in format specified with --input).')
    print_args.add_argument('--input', default=PrintInput.KAST_JSON, type=PrintInput, choices=list(PrintInput))
    print_args.add_argument('--omit-labels', default='', nargs='?', help='List of labels to omit from output.')
    print_args.add_argument(
        '--keep-cells', default='', nargs='?', help='List of cells with primitive values to keep in output.'
    )
    print_args.add_argument('--output-file', type=FileType('w'), default='-')

    rpc_print_args = pyk_args_command.add_parser(
        'rpc-print',
        help='Pretty-print an RPC request/response',
        parents=[k_cli_args.logging_args],
    )
    rpc_print_args.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')
    rpc_print_args.add_argument(
        'input_file',
        type=FileType('r'),
        help='An input file containing the JSON RPC request or response with KoreJSON payload.',
    )
    rpc_print_args.add_argument('--output-file', type=FileType('w'), default='-')

    rpc_kast_args = pyk_args_command.add_parser(
        'rpc-kast',
        help='Convert an "execute" JSON RPC response to a new "execute" or "simplify" request, copying parameters from a reference request.',
        parents=[k_cli_args.logging_args],
    )
    rpc_kast_args.add_argument(
        'reference_request_file',
        type=FileType('r'),
        help='An input file containing a JSON RPC request to server as a reference for the new request.',
    )
    rpc_kast_args.add_argument(
        'response_file',
        type=FileType('r'),
        help='An input file containing a JSON RPC response with KoreJSON payload.',
    )
    rpc_kast_args.add_argument('--output-file', type=FileType('w'), default='-')

    prove_legacy_args = pyk_args_command.add_parser(
        'prove-legacy',
        help='Prove an input specification (using kprovex).',
        parents=[k_cli_args.logging_args],
    )
    prove_legacy_args.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')
    prove_legacy_args.add_argument('main_file', type=str, help='Main file used for kompilation.')
    prove_legacy_args.add_argument('spec_file', type=str, help='File with the specification module.')
    prove_legacy_args.add_argument('spec_module', type=str, help='Module with claims to be proven.')
    prove_legacy_args.add_argument('--output-file', type=FileType('w'), default='-')
    prove_legacy_args.add_argument('kArgs', nargs='*', help='Arguments to pass through to K invocation.')

    kompile_args = pyk_args_command.add_parser(
        'kompile',
        help='Kompile the K specification.',
        parents=[k_cli_args.logging_args],
    )
    kompile_args.add_argument('main_file', type=str, help='File with the specification module.')
    kompile_args.add_argument(
        '--output-definition',
        '--definition',
        type=ensure_dir_path,
        dest='definition_dir',
        help='Path to kompile definition to.',
    )
    kompile_args.add_argument(
        '--backend',
        type=KompileBackend,
        dest='backend',
        default=KompileBackend.LLVM,
        help='K backend to target with compilation.',
    )
    kompile_args.add_argument(
        '--type-inference-mode', type=TypeInferenceMode, help='Mode for doing K rule type inference in.'
    )

    prove_args = pyk_args_command.add_parser(
        'prove',
        help='Prove an input specification (using RPC based prover).',
        parents=[k_cli_args.logging_args],
    )
    prove_args.add_argument('spec_file', type=str, help='File with the specification module.')
    prove_args.add_argument('--definition', type=dir_path, dest='definition_dir', help='Path to definition to use.')
    prove_args.add_argument('--spec-module', dest='spec_module', type=str, help='Module with claims to be proven.')
    prove_args.add_argument(
        '--type-inference-mode', type=TypeInferenceMode, help='Mode for doing K rule type inference in.'
    )
    prove_args.add_argument(
        '--failure-info',
        default=False,
        action='store_true',
        help='Print out more information about proof failures.',
    )

    graph_imports_args = pyk_args_command.add_parser(
        'graph-imports',
        help='Graph the imports of a given definition.',
        parents=[k_cli_args.logging_args],
    )
    graph_imports_args.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')

    coverage_args = pyk_args_command.add_parser(
        'coverage',
        help='Convert coverage file to human readable log.',
        parents=[k_cli_args.logging_args],
    )
    coverage_args.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')
    coverage_args.add_argument('coverage_file', type=FileType('r'), help='Coverage file to build log for.')
    coverage_args.add_argument('-o', '--output', type=FileType('w'), default='-')

    pyk_args_command.add_parser('kore-to-json', help='Convert textual KORE to JSON', parents=[k_cli_args.logging_args])

    pyk_args_command.add_parser('json-to-kore', help='Convert JSON to textual KORE', parents=[k_cli_args.logging_args])

    return pyk_args


if __name__ == '__main__':
    main()
