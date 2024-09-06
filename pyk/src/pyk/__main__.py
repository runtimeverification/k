from __future__ import annotations

import json
import logging
import sys
from collections.abc import Iterable
from contextlib import contextmanager
from pathlib import Path
from subprocess import CalledProcessError
from tempfile import NamedTemporaryFile
from typing import TYPE_CHECKING

from graphviz import Digraph

from .cli.pyk import PrintInput, create_argument_parser, generate_options, parse_toml_args
from .cli.utils import LOG_FORMAT, loglevel
from .coverage import get_rule_by_id, strip_coverage_logger
from .cterm import CTerm
from .cterm.symbolic import cterm_symbolic
from .kast import KAst
from .kast.att import KAtt
from .kast.inner import KInner
from .kast.manip import (
    flatten_label,
    minimize_rule_like,
    minimize_term,
    propagate_up_constraints,
    remove_source_map,
    split_config_and_constraints,
)
from .kast.outer import KFlatModule, read_kast_definition
from .kast.pretty import PrettyPrinter
from .kast.utils import parse_outer
from .kcfg import KCFGExplore
from .kore.parser import KoreParser
from .kore.rpc import ExecuteResult, StopReason
from .kore.syntax import Pattern, kore_term
from .ktool.kompile import Kompile, KompileBackend
from .ktool.kprint import KPrint
from .ktool.kprove import KProve
from .ktool.krun import KRun
from .ktool.prove_rpc import ProveRpc
from .prelude.k import GENERATED_TOP_CELL
from .prelude.ml import is_top, mlAnd, mlOr
from .proof.reachability import APRFailureInfo, APRProof
from .proof.show import APRProofNodePrinter, APRProofShow
from .utils import check_file_path, ensure_dir_path, exit_with_process_error

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Any, Final

    from .cli.pyk import (
        CoverageOptions,
        GraphImportsOptions,
        JsonToKoreOptions,
        KompileCommandOptions,
        KompileXCommandOptions,
        KoreToJsonOptions,
        ParseOuterOptions,
        PrintOptions,
        ProveLegacyOptions,
        ProveOptions,
        RPCKastOptions,
        RPCPrintOptions,
        RunOptions,
    )


_LOGGER: Final = logging.getLogger(__name__)


def main() -> None:
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10**7)

    logging.basicConfig(format=LOG_FORMAT)

    cli_parser = create_argument_parser()
    args = cli_parser.parse_args()
    toml_args = parse_toml_args(args)

    stripped_args = toml_args | {
        key: val for (key, val) in vars(args).items() if val is not None and not (isinstance(val, Iterable) and not val)
    }

    options = generate_options(stripped_args)

    logging.basicConfig(level=loglevel(args), format=LOG_FORMAT, force=True)

    executor_name = 'exec_' + args.command.lower().replace('-', '_')
    if executor_name not in globals():
        raise AssertionError(f'Unimplemented command: {args.command}')

    execute = globals()[executor_name]
    execute(options)


def exec_print(options: PrintOptions) -> None:
    kompiled_dir: Path = options.definition_dir
    printer = KPrint(kompiled_dir)
    if options.input == PrintInput.KORE_JSON:
        _LOGGER.info(f'Reading Kore JSON from file: {options.term.name}')
        kore = Pattern.from_json(options.term.read())
        term = printer.kore_to_kast(kore)
    else:
        _LOGGER.info(f'Reading Kast JSON from file: {options.term.name}')
        term = KInner.from_json(options.term.read())
    if is_top(term):
        options.output_file.write(printer.pretty_print(term))
        _LOGGER.info(f'Wrote file: {options.output_file.name}')
    else:
        if options.minimize:
            if options.omit_labels is not None and options.keep_cells is not None:
                raise ValueError('You cannot use both --omit-labels and --keep-cells.')

            abstract_labels = options.omit_labels.split(',') if options.omit_labels is not None else []
            keep_cells = options.keep_cells.split(',') if options.keep_cells is not None else []
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

        options.output_file.write(printer.pretty_print(term))
        _LOGGER.info(f'Wrote file: {options.output_file.name}')


def exec_rpc_print(options: RPCPrintOptions) -> None:
    kompiled_dir: Path = options.definition_dir
    printer = KPrint(kompiled_dir)
    input_dict = json.loads(options.input_file.read())
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
        if options.output_file is not None:
            options.output_file.write('\n'.join(output_buffer))
        else:
            print('\n'.join(output_buffer))
    except ValueError as e:
        # shorten and print the error message in case kore_to_kast throws ValueError
        _LOGGER.critical(str(e)[:200])
        exit(1)


def exec_rpc_kast(options: RPCKastOptions) -> None:
    """Convert an 'execute' JSON RPC response to a new 'execute' or 'simplify' request.

    Copies parameters from a reference request.
    """
    reference_request = json.loads(options.reference_request_file.read())
    input_dict = json.loads(options.response_file.read())
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
    options.output_file.write(json.dumps(request))


def exec_prove_legacy(options: ProveLegacyOptions) -> None:
    kompiled_dir: Path = options.definition_dir
    kprover = KProve(kompiled_dir, options.main_file)
    final_state = kprover.prove(Path(options.spec_file), spec_module_name=options.spec_module, args=options.k_args)
    options.output_file.write(json.dumps(mlOr([state.kast for state in final_state]).to_dict()))
    _LOGGER.info(f'Wrote file: {options.output_file.name}')


def exec_prove(options: ProveOptions) -> None:
    kompiled_directory: Path
    if options.definition_dir is None:
        kompiled_directory = Kompile.default_directory()
        _LOGGER.info(f'Using kompiled directory: {kompiled_directory}.')
    else:
        kompiled_directory = options.definition_dir

    kprove = KProve(kompiled_directory, use_directory=options.temp_directory)

    @contextmanager
    def explore_context() -> Iterator[KCFGExplore]:
        with cterm_symbolic(
            definition=kprove.definition,
            definition_dir=kprove.definition_dir,
        ) as cts:
            yield KCFGExplore(cts)

    prove_rpc = ProveRpc(kprove, explore_context)

    try:
        proofs = prove_rpc.prove_rpc(options=options)
    except CalledProcessError as err:
        exit_with_process_error(err)
    for proof in sorted(proofs, key=lambda p: p.id):
        print('\n'.join(proof.summary.lines))
        if proof.failed and options.failure_info:
            failure_info = proof.failure_info
            if type(failure_info) is APRFailureInfo:
                print('\n'.join(failure_info.print()))
        if options.show_kcfg and type(proof) is APRProof:
            node_printer = APRProofNodePrinter(proof, kprove, full_printer=True, minimize=False)
            show = APRProofShow(kprove, node_printer=node_printer)
            print('\n'.join(show.show(proof, minimize=False)))
    sys.exit(len([p.id for p in proofs if not p.passed]))


def exec_show(options: ProveOptions) -> None:
    options.max_iterations = 0
    options.show_kcfg = True
    exec_prove(options)


def exec_kompile(options: KompileCommandOptions) -> None:
    main_file = Path(options.main_file)
    check_file_path(main_file)

    kompiled_directory: Path
    if options.definition_dir is None:
        kompiled_directory = Path(f'{main_file.stem}-kompiled')
        ensure_dir_path(kompiled_directory)
    else:
        kompiled_directory = options.definition_dir

    kompile_dict: dict[str, Any] = {
        'main_file': main_file,
        'backend': options.backend.value,
        'syntax_module': options.syntax_module,
        'main_module': options.main_module,
        'md_selector': options.md_selector,
        'include_dirs': options.includes,
        'emit_json': options.emit_json,
        'coverage': options.coverage,
        'gen_bison_parser': options.gen_bison_parser,
        'gen_glr_bison_parser': options.gen_glr_bison_parser,
        'bison_lists': options.bison_lists,
        'outer_parsed_json': options.outer_parsed_json,
    }
    if options.backend == KompileBackend.LLVM:
        kompile_dict['ccopts'] = options.ccopts
        kompile_dict['enable_search'] = options.enable_search
        kompile_dict['llvm_kompile_type'] = options.llvm_kompile_type
        kompile_dict['llvm_kompile_output'] = options.llvm_kompile_output
        kompile_dict['llvm_proof_hint_instrumentation'] = options.llvm_proof_hint_instrumentation
        kompile_dict['llvm_proof_hint_debugging'] = options.llvm_proof_hint_debugging
    elif len(options.ccopts) > 0:
        raise ValueError(f'Option `-ccopt` requires `--backend llvm`, not: --backend {options.backend.value}')
    elif options.enable_search:
        raise ValueError(f'Option `--enable-search` requires `--backend llvm`, not: --backend {options.backend.value}')
    elif options.llvm_kompile_type:
        raise ValueError(
            f'Option `--llvm-kompile-type` requires `--backend llvm`, not: --backend {options.backend.value}'
        )
    elif options.llvm_kompile_output:
        raise ValueError(
            f'Option `--llvm-kompile-output` requires `--backend llvm`, not: --backend {options.backend.value}'
        )
    elif options.llvm_proof_hint_instrumentation:
        raise ValueError(
            f'Option `--llvm-proof-hint-intrumentation` requires `--backend llvm`, not: --backend {options.backend.value}'
        )
    elif options.llvm_proof_hint_debugging:
        raise ValueError(
            f'Option `--llvm-proof-hint-debugging` requires `--backend llvm`, not: --backend {options.backend.value}'
        )

    try:
        Kompile.from_dict(kompile_dict)(
            output_dir=kompiled_directory,
            type_inference_mode=options.type_inference_mode,
            warnings=options.warnings,
            warnings_to_errors=options.warnings_to_errors,
            ignore_warnings=options.ignore_warnings,
            no_exc_wrap=options.no_exc_wrap,
            tool_mode=True,
        )
    except CalledProcessError as err:
        exit_with_process_error(err)


def exec_run(options: RunOptions) -> None:
    pgm_file = Path(options.pgm_file)
    check_file_path(pgm_file)
    kompiled_directory: Path
    if options.definition_dir is None:
        kompiled_directory = Kompile.default_directory()
        _LOGGER.info(f'Using kompiled directory: {kompiled_directory}.')
    else:
        kompiled_directory = options.definition_dir
    krun = KRun(kompiled_directory)
    rc, res = krun.krun(pgm_file)
    print(krun.pretty_print(res))
    sys.exit(rc)


def exec_graph_imports(options: GraphImportsOptions) -> None:
    kompiled_dir: Path = options.definition_dir
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


def exec_coverage(options: CoverageOptions) -> None:
    kompiled_dir: Path = options.definition_dir
    definition = remove_source_map(read_kast_definition(kompiled_dir / 'compiled.json'))
    pretty_printer = PrettyPrinter(definition)
    for rid in options.coverage_file:
        rule = minimize_rule_like(strip_coverage_logger(get_rule_by_id(definition, rid.strip())))
        options.output_file.write('\n\n')
        options.output_file.write('Rule: ' + rid.strip())
        options.output_file.write('\nUnparsed:\n')
        options.output_file.write(pretty_printer.print(rule))
    _LOGGER.info(f'Wrote file: {options.output_file.name}')


def exec_kore_to_json(options: KoreToJsonOptions) -> None:
    text = sys.stdin.read()
    kore = KoreParser(text).pattern()
    print(kore.json)


def exec_json_to_kore(options: JsonToKoreOptions) -> None:
    text = sys.stdin.read()
    kore = Pattern.from_json(text)
    kore.write(sys.stdout)
    sys.stdout.write('\n')


def exec_parse_outer(options: ParseOuterOptions) -> None:
    definition_file = options.main_file.resolve()
    main_module_name = options.main_module or definition_file.stem.upper()

    final_definition = parse_outer(
        definition_file,
        main_module_name,
        include_dirs=options.includes,
        md_selector=options.md_selector,
    )

    result_text = json.dumps(final_definition.to_dict())
    try:
        options.output_file.write(result_text)
    except AttributeError:
        sys.stdout.write(f'{result_text}\n')


def exec_kompilex(options: KompileXCommandOptions) -> None:
    definition_file = Path(options.main_file).resolve()
    main_module_name = options.main_module or definition_file.stem.upper()

    final_definition = parse_outer(
        definition_file,
        main_module_name,
        include_dirs=options.includes,
        md_selector=options.md_selector,
    )

    if options.pre_parsed_prelude:
        prelude_json = json.loads(options.pre_parsed_prelude.read())
        prelude_modules = tuple(KFlatModule.from_dict(mod) for mod in prelude_json)
        final_definition = final_definition.let(all_modules=final_definition.all_modules + prelude_modules)

    syntax_module_name = options.syntax_module or main_module_name + '-SYNTAX'
    if syntax_module_name not in [m.name for m in final_definition.all_modules]:
        base_msg = f'Could not find main syntax module with name {syntax_module_name} in definition.'
        if options.syntax_module:
            _LOGGER.error(base_msg)
            exit(1)
        else:
            _LOGGER.warn(f'{base_msg} Use --syntax-module to specify one. Using {main_module_name} as default.')
        syntax_module_name = main_module_name
    syntax_att = KAtt.parse({'syntaxModule': main_module_name})

    final_definition = final_definition.let_att(syntax_att)

    kast_json = {'format': 'KAST', 'version': KAst.version(), 'term': final_definition.to_dict()}

    with NamedTemporaryFile('w', prefix='pyk_kompilex_', delete=not options.debug) as ntf:
        ntf.write(json.dumps(kast_json))
        ntf.flush()

        options.main_file = ntf.name
        options.outer_parsed_json = True
        if options.definition_dir is None:
            options.definition_dir = Path(f'{definition_file.stem}-kompiled')

        exec_kompile(options)


if __name__ == '__main__':
    main()
