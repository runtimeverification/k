from __future__ import annotations

import json
import logging
import sys
from pathlib import Path
from typing import TYPE_CHECKING

from graphviz import Digraph

from .cli.args import (
    DefinitionOptionsGroup,
    DisplayOptionsGroup,
    IntOption,
    KDefinitionOptionsGroup,
    KompileOptionsGroup,
    LoggingOptionsGroup,
    OutputFileOptionsGroup,
    SaveDirOptionsGroup,
    SpecOptionsGroup,
    StringListOption,
    WarningOptionsGroup,
)
from .cli.cli import CLI, BoolOption, Command, DirPathOption, EnumOption, ReadFileOption, StringOption
from .cli.pyk import PrintInput
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
from .ktool._ktool import TypeInferenceMode
from .ktool.kompile import Kompile, KompileBackend
from .ktool.kprint import KPrint
from .ktool.kprove import KProve
from .ktool.krun import KRun
from .prelude.k import GENERATED_TOP_CELL
from .prelude.ml import is_top, mlAnd, mlOr
from .proof.reachability import APRFailureInfo, APRProof
from .proof.show import APRProofNodePrinter, APRProofShow
from .utils import check_file_path, ensure_dir_path, exit_with_process_error

if TYPE_CHECKING:
    from typing import IO, Any, Final, Iterable


_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10**7)

    cli = CLI([JsonToKoreCommand(), JsonToKoreCommand(), CoverageCommand()])
    cli.get_and_exec_command()


class PrintOptionsGroup(DefinitionOptionsGroup, OutputFileOptionsGroup, DisplayOptionsGroup, LoggingOptionsGroup):
    term: IO[Any]
    input: PrintInput
    omit_labels: str | None
    keep_cells: str | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            ReadFileOption(name='term', optional=False, help_str='Input term (in format specified with --input)')
        )
        self.add_option(
            EnumOption(
                name='input',
                cmd_line_name='--input',
                optional=True,
                default=PrintInput.KAST_JSON,
                help_str='Input format.',
                enum_type=PrintInput,
            )
        )
        self.add_option(
            StringOption(
                name='omit_labels',
                cmd_line_name='--omit-labels',
                optional=True,
                default=None,
                help_str='List of labels to omit from output',
            )
        )
        self.add_option(
            StringOption(
                name='keep_cells',
                cmd_line_name='--keep-cells',
                optional=True,
                default=None,
                help_str='List of cells with primitive values to keep in output',
            )
        )


class PrintCommand(Command[PrintOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('print', 'Pretty print a term.', PrintOptionsGroup())

    def exec(self) -> None:
        kompiled_dir: Path = self.options.definition_dir
        printer = KPrint(kompiled_dir)
        if self.options.input == PrintInput.KORE_JSON:
            _LOGGER.info(f'Reading Kore JSON from file: {self.options.term.name}')
            kore = Pattern.from_json(self.options.term.read())
            term = printer.kore_to_kast(kore)
        else:
            _LOGGER.info(f'Reading Kast JSON from file: {self.options.term.name}')
            term = KInner.from_json(self.options.term.read())
        if is_top(term):
            self.options.output_file.write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {self.options.output_file.name}')
        else:
            if self.options.minimize:
                if self.options.omit_labels is not None and self.options.keep_cells is not None:
                    raise ValueError('You cannot use both --omit-labels and --keep-cells.')

                abstract_labels = self.options.omit_labels.split(',') if self.options.omit_labels is not None else []
                keep_cells = self.options.keep_cells.split(',') if self.options.keep_cells is not None else []
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

            self.options.output_file.write(printer.pretty_print(term))
            _LOGGER.info(f'Wrote file: {self.options.output_file.name}')


class RPCPrintOptionsGroup(DefinitionOptionsGroup, OutputFileOptionsGroup, LoggingOptionsGroup):
    input_file: IO[Any]

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            ReadFileOption(
                'input_file',
                optional=False,
                help_str='An input file containing the JSON RPC request or response with KoreJSON payload.',
            )
        )


class RPCPrintCommand(Command[RPCPrintOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('rpc-print', 'Pretty-print an RPC request/response', RPCPrintOptionsGroup())

    def exec(self) -> None:
        kompiled_dir: Path = self.options.definition_dir
        printer = KPrint(kompiled_dir)
        input_dict = json.loads(self.options.input_file.read())
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
            if self.options.output_file is not None:
                self.options.output_file.write('\n'.join(output_buffer))
            else:
                print('\n'.join(output_buffer))
        except ValueError as e:
            # shorten and print the error message in case kore_to_kast throws ValueError
            _LOGGER.critical(str(e)[:200])
            exit(1)


class RPCKastOptionsGroup(OutputFileOptionsGroup, LoggingOptionsGroup):
    reference_request_file: IO[Any]
    response_file: IO[Any]

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            ReadFileOption(
                name='reference_request_file',
                optional=False,
                help_str='An input file containing a JSON RPC request to server as a reference for the new request.',
            )
        )
        self.add_option(
            ReadFileOption(
                name='response_file',
                optional=False,
                help_str='An input file containing a JSON RPC reesponse with KoreJSON payload.',
            )
        )


class RPCKastCommand(Command[RPCKastOptionsGroup]):
    def __init__(self) -> None:
        super().__init__(
            'rpc-kast',
            'Convert an "execute" JSON RPC response to a new "execute" or "simplify" request, copying paraemeters from a reference request.',
            RPCKastOptionsGroup(),
        )

    def exec(self) -> None:
        """
        Convert an 'execute' JSON RPC response to a new 'execute' or 'simplify' request,
        copying parameters from a reference request.
        """
        reference_request = json.loads(self.options.reference_request_file.read())
        input_dict = json.loads(self.options.response_file.read())
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
        self.options.output_file.write(json.dumps(request))


class ProveLegacyOptionsGroup(DefinitionOptionsGroup, OutputFileOptionsGroup, LoggingOptionsGroup):
    main_file: Path
    spec_file: Path
    spec_module: str
    k_args: Iterable[str]

    def __init__(self) -> None:
        super().__init__()

        self.add_option(DirPathOption(name='main_file', help_str='Main file used for kompilation', optional=False))
        self.add_option(DirPathOption(name='spec_file', help_str='File with the specification module.', optional=False))
        self.add_option(StringOption(name='spec_module', help_str='Module with claims to be proven', optional=False))
        self.add_option(
            StringListOption(
                name='k_args',
                cmd_line_name='kArgs',
                toml_name='kArgs',
                help_str='Arguments to pass through to K invocation.',
                optional=True,
            )
        )


class ProveLegacyCommand(Command[ProveLegacyOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('prove-legacy', 'Prove an input specification (using kprovex).', ProveLegacyOptionsGroup())

    def exec(self) -> None:
        kompiled_dir: Path = self.options.definition_dir
        kprover = KProve(kompiled_dir, self.options.main_file)
        final_state = kprover.prove(
            Path(self.options.spec_file), spec_module_name=self.options.spec_module, args=self.options.k_args
        )
        self.options.output_file.write(json.dumps(mlOr([state.kast for state in final_state]).to_dict()))
        _LOGGER.info(f'Wrote file: {self.options.output_file.name}')


class ProveOptionsGroup(LoggingOptionsGroup, SpecOptionsGroup, SaveDirOptionsGroup):
    definition_dir: Path | None
    type_inference_mode: TypeInferenceMode | None
    failure_info: bool
    kore_rpc_command: str | Iterable[str] | None
    max_depth: int | None
    max_iterations: int | None
    show_kcfg: bool

    def __init__(self) -> None:
        super().__init__()

        self.add_option(
            DirPathOption(
                name='definition_dir',
                cmd_line_name='--definition',
                toml_name='definition',
                help_str='Path to definition to use.',
                optional=True,
                default=None,
            )
        )
        self.add_option(
            EnumOption(
                enum_type=TypeInferenceMode,
                name='type_inference_mode',
                cmd_line_name='--type-inference-mode',
                help_str='Mode for doing K rule type inference in.',
                optional=True,
                default=None,
            )
        )
        self.add_option(
            BoolOption(
                name='failure_info',
                cmd_line_name='--failure-info',
                help_str='Print out more information about proof failures.',
                default=None,
            )
        )
        self.add_option(
            StringOption(
                name='kore_rpc_command',
                cmd_line_name='--kore-rpc-command',
                help_str='Custom command to start RPC server',
                default=None,
            )
        )
        self.add_option(
            IntOption(
                name='max_depth',
                cmd_line_name='--max-depth',
                help_str='Maximum number of steps to take in symbolic execution per basic block.',
                default=None,
                optional=True,
            )
        )
        self.add_option(
            IntOption(
                name='max_iterations',
                cmd_line_name='--max-iterations',
                help_str='Maximum number of KCFG explorations to take in attempting to discharge proof.',
                default=None,
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='show_kcfg',
                cmd_line_name='--show-kcfg',
                help_str='Display the resulting proof KCFG.',
                default=False,
                optional=True,
            )
        )


class ProveCommand(Command[ProveOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('prove', 'Prove an input specification (using RPC based prover).', ProveOptionsGroup())

    def exec(self) -> None:
        kompiled_directory: Path
        if self.options.definition_dir is None:
            kompiled_directory = Kompile.default_directory()
            _LOGGER.info(f'Using kompiled directory: {kompiled_directory}.')
        else:
            kompiled_directory = self.options.definition_dir
        kprove = KProve(kompiled_directory, use_directory=self.options.temp_directory)
        try:
            proofs = kprove.prove_rpc(options=self.options)
        except RuntimeError as err:
            _, _, _, cpe = err.args
            exit_with_process_error(cpe)
        for proof in sorted(proofs, key=lambda p: p.id):
            print('\n'.join(proof.summary.lines))
            if proof.failed and self.options.failure_info:
                failure_info = proof.failure_info
                if type(failure_info) is APRFailureInfo:
                    print('\n'.join(failure_info.print()))
            if self.options.show_kcfg and type(proof) is APRProof:
                node_printer = APRProofNodePrinter(proof, kprove, full_printer=True, minimize=False)
                show = APRProofShow(kprove, node_printer=node_printer)
                print('\n'.join(show.show(proof)))
        sys.exit(len([p.id for p in proofs if not p.passed]))


class ShowCommand(ProveCommand):
    def __init__(self) -> None:
        Command.__init__(self, 'show', 'Display the status of a given proof', ProveOptionsGroup())

    def exec(self) -> None:
        self.options.max_iterations = 0
        self.options.show_kcfg = True
        super().exec()


class KompileCommandOptionsGroup(
    LoggingOptionsGroup, WarningOptionsGroup, KDefinitionOptionsGroup, KompileOptionsGroup
):
    definition_dir: Path | None
    main_file: str
    backend: KompileBackend
    type_inference_mode: TypeInferenceMode | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            DirPathOption(
                name='definition_dir',
                cmd_line_name='--output-definition',
                aliases=['--definition'],
                toml_name='definition',
                default=None,
                help_str='Path to kompile definition to.',
                optional=True,
            )
        )
        self.add_option(
            StringOption(
                name='main_file',
                optional=False,
                help_str='File with the specification module.',
            )
        )
        self.add_option(
            EnumOption(
                enum_type=KompileBackend,
                name='backend',
                cmd_line_name='--backend',
                default=KompileBackend.LLVM,
                help_str='K backend to target with compilation.',
                optional=True,
            )
        )
        self.add_option(
            EnumOption(
                enum_type=TypeInferenceMode,
                name='type_inference_mode',
                cmd_line_name='--type-inference-mode',
                default=None,
                help_str='Mode for doing K rule type inference in.',
                optional=True,
            )
        )


class KompileCommand(Command[KompileCommandOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('kompile', 'Kompile the K specification', KompileCommandOptionsGroup())

    def exec(self) -> None:
        main_file = Path(self.options.main_file)
        check_file_path(main_file)

        kompiled_directory: Path
        if self.options.definition_dir is None:
            kompiled_directory = Path(f'{main_file.stem}-kompiled')
            ensure_dir_path(kompiled_directory)
        else:
            kompiled_directory = self.options.definition_dir

        kompile_dict: dict[str, Any] = {
            'main_file': main_file,
            'backend': self.options.backend.value,
            'syntax_module': self.options.syntax_module,
            'main_module': self.options.main_module,
            'md_selector': self.options.md_selector,
            'include_dirs': (Path(include) for include in self.options.includes),
            'emit_json': self.options.emit_json,
            'coverage': self.options.coverage,
            'gen_bison_parser': self.options.gen_bison_parser,
            'gen_glr_bison_parser': self.options.gen_glr_bison_parser,
            'bison_lists': self.options.bison_lists,
        }
        if self.options.backend == KompileBackend.LLVM:
            kompile_dict['ccopts'] = self.options.ccopts
            kompile_dict['enable_search'] = self.options.enable_search
            kompile_dict['llvm_kompile_type'] = self.options.llvm_kompile_type
            kompile_dict['llvm_kompile_output'] = self.options.llvm_kompile_output
            kompile_dict['llvm_proof_hint_instrumentation'] = self.options.llvm_proof_hint_instrumentation
        elif len(self.options.ccopts) > 0:
            raise ValueError(f'Option `-ccopt` requires `--backend llvm`, not: --backend {self.options.backend.value}')
        elif self.options.enable_search:
            raise ValueError(
                f'Option `--enable-search` requires `--backend llvm`, not: --backend {self.options.backend.value}'
            )
        elif self.options.llvm_kompile_type:
            raise ValueError(
                f'Option `--llvm-kompile-type` requires `--backend llvm`, not: --backend {self.options.backend.value}'
            )
        elif self.options.llvm_kompile_output:
            raise ValueError(
                f'Option `--llvm-kompile-output` requires `--backend llvm`, not: --backend {self.options.backend.value}'
            )
        elif self.options.llvm_proof_hint_instrumentation:
            raise ValueError(
                f'Option `--llvm-proof-hint-intrumentation` requires `--backend llvm`, not: --backend {self.options.backend.value}'
            )

        try:
            Kompile.from_dict(kompile_dict)(
                output_dir=kompiled_directory,
                type_inference_mode=self.options.type_inference_mode,
                warnings=self.options.warnings,
                warnings_to_errors=self.options.warnings_to_errors,
                no_exc_wrap=self.options.no_exc_wrap,
            )
        except RuntimeError as err:
            _, _, _, _, cpe = err.args
            exit_with_process_error(cpe)


class RunOptionsGroup(LoggingOptionsGroup):
    pgm_file: str
    definition_dir: Path | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(StringOption(name='pgm_file', optional=False, help_str='File program to run in it.'))
        self.add_option(
            DirPathOption(
                name='definition_dir',
                cmd_line_name='--definition',
                optional=False,
                help_str='Path to definition to use.',
            )
        )


class RunCommand(Command[RunOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('run', 'Run a given program using the K definition.', RunOptionsGroup())

    def exec(self) -> None:
        pgm_file = Path(self.options.pgm_file)
        check_file_path(pgm_file)
        kompiled_directory: Path
        if self.options.definition_dir is None:
            kompiled_directory = Kompile.default_directory()
            _LOGGER.info(f'Using kompiled directory: {kompiled_directory}.')
        else:
            kompiled_directory = self.options.definition_dir
        krun = KRun(kompiled_directory)
        rc, res = krun.krun(pgm_file)
        print(krun.pretty_print(res))
        sys.exit(rc)


class GraphImportsOptionsGroup(DefinitionOptionsGroup, LoggingOptionsGroup): ...


class GraphImportsCommand(Command[GraphImportsOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('graph-imports', 'Graph the imports of a given definition', GraphImportsOptionsGroup())

    def exec(self) -> None:
        kompiled_dir: Path = self.options.definition_dir
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


class CoverageOptionsGroup(DefinitionOptionsGroup, OutputFileOptionsGroup, LoggingOptionsGroup):
    coverage_file: IO[Any]

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            ReadFileOption(name='coverage_file', optional=False, help_str='Coverage fild to build log for.')
        )


class CoverageCommand(Command[CoverageOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('coverage-options', 'Convert coverage file to human readable log.', CoverageOptionsGroup())

    def exec(self) -> None:
        kompiled_dir: Path = self.options.definition_dir
        definition = remove_source_map(read_kast_definition(kompiled_dir / 'compiled.json'))
        pretty_printer = PrettyPrinter(definition)
        for rid in self.options.coverage_file:
            rule = minimize_rule(strip_coverage_logger(get_rule_by_id(definition, rid.strip())))
            self.options.output_file.write('\n\n')
            self.options.output_file.write('Rule: ' + rid.strip())
            self.options.output_file.write('\nUnparsed:\n')
            self.options.output_file.write(pretty_printer.print(rule))
        _LOGGER.info(f'Wrote file: {self.options.output_file.name}')


class KoreToJsonCommand(Command[LoggingOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('kore-to-json', 'convert textual KORE to JSON', LoggingOptionsGroup())

    def exec(self) -> None:
        text = sys.stdin.read()
        kore = KoreParser(text).pattern()
        print(kore.json)


class JsonToKoreCommand(Command[LoggingOptionsGroup]):
    def __init__(self) -> None:
        super().__init__('json-to-kore', 'convert JSON to textual KORE', LoggingOptionsGroup())

    def exec(self) -> None:
        text = sys.stdin.read()
        kore = Pattern.from_json(text)
        kore.write(sys.stdout)
        sys.stdout.write('\n')


if __name__ == '__main__':
    main()
