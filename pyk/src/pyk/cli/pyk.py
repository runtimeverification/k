from __future__ import annotations

import json
import sys
from argparse import FileType
from enum import Enum
from pathlib import Path
from typing import IO, TYPE_CHECKING, Any

from graphviz import Digraph

from pyk.coverage import get_rule_by_id, strip_coverage_logger
from pyk.cterm import CTerm
from pyk.kast.inner import KInner
from pyk.kast.manip import (
    flatten_label,
    minimize_rule,
    minimize_term,
    propagate_up_constraints,
    remove_source_map,
    split_config_and_constraints,
)
from pyk.kast.outer import read_kast_definition
from pyk.kast.pretty import PrettyPrinter
from pyk.kore.parser import KoreParser
from pyk.kore.rpc import ExecuteResult, StopReason
from pyk.kore.syntax import Pattern, kore_term
from pyk.ktool.kprint import KPrint
from pyk.ktool.kprove import KProve
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.ml import is_top, mlAnd, mlOr
from pyk.utils import _LOGGER

from .args import DefinitionOptions, DisplayOptions, LoggingOptions, OutputFileOptions
from .cli import Command

if TYPE_CHECKING:
    from argparse import ArgumentParser
    from collections.abc import Iterable


class PrintInput(Enum):
    KORE_JSON = 'kore-json'
    KAST_JSON = 'kast-json'


class JsonToKoreCommand(Command, LoggingOptions):
    @staticmethod
    def name() -> str:
        return 'json-to-kore'

    @staticmethod
    def help_str() -> str:
        return 'Convert JSON to textual KORE'

    def exec(self) -> None:
        text = sys.stdin.read()
        kore = Pattern.from_json(text)
        kore.write(sys.stdout)
        sys.stdout.write('\n')


class KoreToJsonCommand(Command, LoggingOptions):
    @staticmethod
    def name() -> str:
        return 'kore-to-json'

    @staticmethod
    def help_str() -> str:
        return 'Convert textual KORE to JSON'

    def exec(self) -> None:
        text = sys.stdin.read()
        kore = KoreParser(text).pattern()
        print(kore.json)


class CoverageCommand(Command, DefinitionOptions, OutputFileOptions, LoggingOptions):
    coverage_file: IO[Any]

    @staticmethod
    def name() -> str:
        return 'coverage'

    @staticmethod
    def help_str() -> str:
        return 'Convert coverage file to human readable log.'

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('coverage_file', type=FileType('r'), help='Coverage file to build log for.')

    def exec(self) -> None:
        kompiled_dir: Path = self.definition_dir
        definition = remove_source_map(read_kast_definition(kompiled_dir / 'compiled.json'))
        pretty_printer = PrettyPrinter(definition)
        for rid in self.coverage_file:
            rule = minimize_rule(strip_coverage_logger(get_rule_by_id(definition, rid.strip())))
            self.output_file.write('\n\n')
            self.output_file.write('Rule: ' + rid.strip())
            self.output_file.write('\nUnparsed:\n')
            self.output_file.write(pretty_printer.print(rule))
        _LOGGER.info(f'Wrote file: {self.output_file.name}')


class GraphImportsCommand(Command, DefinitionOptions, LoggingOptions):
    @staticmethod
    def name() -> str:
        return 'graph-imports'

    @staticmethod
    def help_str() -> str:
        return 'Graph the imports of a given definition.'

    def exec(self) -> None:
        kompiled_dir: Path = self.definition_dir
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


class RPCKastCommand(Command, OutputFileOptions, LoggingOptions):
    reference_request_file: IO[Any]
    response_file: IO[Any]

    @staticmethod
    def name() -> str:
        return 'rpc-kast'

    @staticmethod
    def help_str() -> str:
        return 'Convert an "execute" JSON RPC response to a new "execute" or "simplify" request, copying parameters from a reference request.'

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            'reference_request_file',
            type=FileType('r'),
            help='An input file containing a JSON RPC request to server as a reference for the new request.',
        )
        parser.add_argument(
            'response_file',
            type=FileType('r'),
            help='An input file containing a JSON RPC response with KoreJSON payload.',
        )

    def exec(self) -> None:
        """
        Convert an 'execute' JSON RPC response to a new 'execute' or 'simplify' request,
        copying parameters from a reference request.
        """
        reference_request = json.loads(self.reference_request_file.read())
        input_dict = json.loads(self.response_file.read())
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
        self.output_file.write(json.dumps(request))


class RPCPrintCommand(Command, DefinitionOptions, OutputFileOptions, LoggingOptions):
    input_file: IO[Any]

    @staticmethod
    def name() -> str:
        return 'rpc-print'

    @staticmethod
    def help_str() -> str:
        return 'Pretty-print an RPC request/response'

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            'input_file',
            type=FileType('r'),
            help='An input file containing the JSON RPC request or response with KoreJSON payload.',
        )

    def exec(self) -> None:
        kompiled_dir: Path = self.definition_dir
        printer = KPrint(kompiled_dir)
        input_dict = json.loads(self.input_file.read())
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
            if self.output_file is not None:
                self.output_file.write('\n'.join(output_buffer))
            else:
                print('\n'.join(output_buffer))
        except ValueError as e:
            # shorten and print the error message in case kore_to_kast throws ValueError
            _LOGGER.critical(str(e)[:200])
            exit(1)


class PrintCommand(Command, DefinitionOptions, OutputFileOptions, DisplayOptions, LoggingOptions):
    term: IO[Any]
    input: PrintInput
    minimize: bool
    omit_labels: str | None
    keep_cells: str | None

    @staticmethod
    def name() -> str:
        return 'print'

    @staticmethod
    def help_str() -> str:
        return 'Pretty print a term.'

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'input': PrintInput.KAST_JSON,
            'omit_labels': None,
            'keep_cells': None,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            'term', type=FileType('r'), help='File containing input term (in format specified with --input).'
        )
        parser.add_argument('--input', type=PrintInput, choices=list(PrintInput))
        parser.add_argument('--omit-labels', nargs='?', help='List of labels to omit from output.')
        parser.add_argument('--keep-cells', nargs='?', help='List of cells with primitive values to keep in output.')

    def exec(self) -> None:
        kompiled_dir: Path = self.definition_dir
        printer = KPrint(kompiled_dir)
        if self.input == PrintInput.KORE_JSON:
            _LOGGER.info(f'Reading Kore JSON from file: {self.term.name}')
            kore = Pattern.from_json(self.term.read())
            term = printer.kore_to_kast(kore)
        else:
            _LOGGER.info(f'Reading Kast JSON from file: {self.term.name}')
            term = KInner.from_json(self.term.read())
        if is_top(term):
            self.output_file.write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {self.output_file.name}')
        else:
            if self.minimize:
                if self.omit_labels != None and self.keep_cells != None:
                    raise ValueError('You cannot use both --omit-labels and --keep-cells.')

                abstract_labels = self.omit_labels.split(',') if self.omit_labels is not None else []
                keep_cells = self.keep_cells.split(',') if self.keep_cells is not None else []
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

            self.output_file.write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {self.output_file.name}')


class ProveLegacyCommand(Command, DefinitionOptions, OutputFileOptions, LoggingOptions):
    main_file: Path
    spec_file: Path
    spec_module: str
    k_args: Iterable[str]

    @staticmethod
    def name() -> str:
        return 'prove-legacy'

    @staticmethod
    def help_str() -> str:
        return 'Prove an input specification (using kprovex).'

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'k_args': [],
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('main_file', type=str, help='Main file used for kompilation.')
        parser.add_argument('spec_file', type=str, help='File with the specification module.')
        parser.add_argument('spec_module', type=str, help='Module with claims to be proven.')
        parser.add_argument('k_args', nargs='*', help='Arguments to pass through to K invocation.')

    def exec(self) -> None:
        kompiled_dir: Path = self.definition_dir
        kprover = KProve(kompiled_dir, self.main_file)
        final_state = kprover.prove(Path(self.spec_file), spec_module_name=self.spec_module, args=self.k_args)
        self.output_file.write(json.dumps(mlOr([state.kast for state in final_state]).to_dict()))
        _LOGGER.info(f'Wrote file: {self.output_file.name}')
