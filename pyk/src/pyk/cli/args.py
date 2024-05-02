from __future__ import annotations

import sys
from argparse import ArgumentParser
from functools import cached_property
from pathlib import Path
from typing import IO, TYPE_CHECKING, Any
from argparse import FileType

from ..ktool.kompile import KompileBackend, LLVMKompileType, TypeInferenceMode, Warnings
from .cli import Option, Options, OptionsGroup
from .utils import bug_report_arg, dir_path, ensure_dir_path, file_path

if TYPE_CHECKING:
    from collections.abc import Iterable

    from ..utils import BugReport


class LoggingOptionsGroup(OptionsGroup):
    def __init__(self) -> None:
        super().__init__()
        self.add_option(Option('--debug', bool, 'debug', 'Debug output.', default=False, action='store_true'))
        self.add_option(
            Option('--verbose', bool, 'verbose', 'Verbose output', default=False, action='store_true', aliases=['-v'])
        )


class LoggingOptions(Options):
    debug: bool
    verbose: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'verbose': False,
            'debug': False,
        }

    @staticmethod
    def from_option_string() -> dict[str, Any]:
        return {
            'v': 'verbose',
        }


class WarningOptionsGroup(OptionsGroup):
    warnings: Warnings | None
    warnings_to_errors: bool

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                '--warnings-to-errors',
                bool,
                'warnings_to_errors',
                'Turn warnings into errors (no effect on pyk, only subcommands).',
                default=False,
                action='store_true',
                toml_name='w2e',
            )
        )
        self.add_option(
            Option(
                '--warnings',
                Warnings,
                'warnings',
                'Warnings to print about (no effect on pyk, only subcommands).',
                default=None,
                toml_name='w',
                choices=list(Warnings),
            )
        )


class WarningOptions(Options):
    warnings: Warnings | None
    warnings_to_errors: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'warnings': None,
            'warnings_to_errors': False,
        }

    @staticmethod
    def from_option_string() -> dict[str, Any]:
        return {
            'w': 'warnings',
            'w2e': 'warning_to_error',
        }


class OutputFileOptionsGroup(OptionsGroup):
    output_file: IO[Any]

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                '--output-file',
                FileType('w'),
                'output_file',
                'Output File',
                default=sys.stdout,
            )
        )


class OutputFileOptions(Options):
    output_file: IO[Any]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output_file': sys.stdout,
        }


class DefinitionOptionsGroup(OptionsGroup):
    definition_dir: Path

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option('--definition', dir_path, 'definition_dir', 'Path to definition to use.', default=None)
        )


class DefinitionOptions(Options):
    definition_dir: Path

    @staticmethod
    def from_option_string() -> dict[str, Any]:
        return {
            'output-definition': 'definition_dir',
            'definition': 'definition_dir',
        }


class DisplayOptionsGroup(OptionsGroup):
    minimize: bool

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                '--minimize', bool, 'minimize', 'Minimize output.', action='store_true', default=True
            )
        )


class DisplayOptions(Options):
    minimize: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'minimize': True,
        }


class KDefinitionOptionsGroup(OptionsGroup):
    includes: list[str]
    main_module: str | None
    syntax_module: str | None
    md_selector: str


    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                '-I', str, 'includes', 'Directories to lookup K definitions in.', action='append', default=[],
                
            )
        )
        self.add_option(
            Option(
                '--main-module', str, 'main_module', 'Name of the main module.', default=None,
                
            )
        )
        self.add_option(
            Option(
                '--syntax-module', str, 'syntax_module', 'Name of the syntax module.', default=None,
                
            )
        )
        self.add_option(
            Option(
                '--md-selector', str, 'md_selector', 'Code selector expression to use when reading markdown.', default='k',
                
            )
        )


class KDefinitionOptions(Options):
    includes: list[str]
    main_module: str | None
    syntax_module: str | None
    spec_module: str | None
    md_selector: str

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'spec_module': None,
            'main_module': None,
            'syntax_module': None,
            'md_selector': 'k',
            'includes': [],
        }



class SaveDirOptionsGroup(OptionsGroup):
    save_directory: Path | None
    temp_directory: Path | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                '--save-directory', ensure_dir_path, 'save_directory', 'Directory to save proof artifacts at for reuse.', default=None,
            )
        )
        self.add_option(
            Option(
                '--temp-directory', ensure_dir_path, 'temp_directory', 'Directory to save proof intermediate temporaries to.', default=None,
            )
        )


class SaveDirOptions(Options):
    save_directory: Path | None
    temp_directory: Path | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'save_directory': None,
            'temp_directory': None,
        }


class SpecOptionsGroup(OptionsGroup):
    spec_file: Path
    spec_module: str | None
    claim_labels: Iterable[str] | None
    exclude_claim_labels: Iterable[str] | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                'spec_file',
                file_path,
                help_str='Path to spec_file.',
                required=True,
            )
        )
        self.add_option(
            Option(
                '--spec-module',
                str,
                'spec_module',
                'Module with claims to be proven.',
                default=None,
            )
        )
        self.add_option(
            Option(
                '--claim',
                str,
                'claim_labels',
                'Only prove listed claims, MODULE_NAME.claim-id',
                action='append',
                default=None,
                toml_name='claim',
            )
        )
        self.add_option(
            Option(
                '--exclude_claim',
                str,
                'exclude_claim_labels',
                'Skip listed claims, MODULE_NAME.claim-id',
                action='append',
                default=None,
                toml_name='exclude-claim',
            )
        )



class SpecOptions(SaveDirOptions):
    spec_file: Path
    spec_module: str | None
    claim_labels: Iterable[str] | None
    exclude_claim_labels: Iterable[str] | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'spec_module': None,
            'claim_labels': None,
            'exclude_claim_labels': None,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return SaveDirOptions.from_option_string() | {
            'claim': 'claim_labels',
            'exclude-claim': 'exclude_claim_labels',
        }


class KompileOptionsGroup(OptionsGroup):
    emit_json: bool
    llvm_kompile: bool
    llvm_library: bool
    enable_llvm_debug: bool
    llvm_kompile_type: LLVMKompileType | None
    llvm_kompile_output: Path | None
    llvm_proof_hint_instrumentation: bool
    read_only: bool
    o0: bool
    o1: bool
    o2: bool
    o3: bool
    ccopts: list[str]
    enable_search: bool
    coverage: bool
    gen_bison_parser: bool
    gen_glr_bison_parser: bool
    bison_lists: bool
    no_exc_wrap: bool


    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option('--emit-json', bool, 'emit_json', 'Emit JSON definition after compilation.', action='store_true', default=False)
        )
        self.add_option(
            Option('--no-llvm-kompile', bool, 'llvm_kompile', 'Do not run llvm-kompile process.', action='store_false', default=True)
        )
        self.add_option(
            Option('--with-llvm-library', bool, 'llvm_library', 'Make kompile generate a dynamic llvm library.', action='store_true', default=False)
        )
        self.add_option(
            Option('--enable-llvm-debug', bool, 'enable_llvm_debug', 'Make kompile generate debug symbols for llvm.', action='store_true', default=False)
        )
        self.add_option(
            Option('--llvm-kompile-type', LLVMKompileType, 'llvm_kompile_type', 'Mode to kompile LLVM backend in.', default=None, choices=list(LLVMKompileType))
        )
        self.add_option(
            Option('--llvm-kompile-output',  ensure_dir_path, 'llvm_kompile_output', 'Location to put kompiled LLVM backend at.', default=None)
        )
        self.add_option(
            Option('--llvm-proof-hint-instrumentation',  bool, 'llvm_proof_hint_instrumentation', 'Enable proof hint generation in LLVM backend kompilation', action='store_true', default=False)
        )
        self.add_option(
            Option('--read-only-kompiled-directory',  bool, 'read_only', 'Generate a kompiled directory that K will not attempt to write to afterwards.', action='store_true', default=False)
        )
        self.add_option(
            Option('-O0',  bool, 'o0', 'Optimization level 0', action='store_true', default=False)
        )
        self.add_option(
            Option('-O1',  bool, 'o1', 'Optimization level 1', action='store_true', default=False)
        )
        self.add_option(
            Option('-O2',  bool, 'o2', 'Optimization level 2', action='store_true', default=False)
        )
        self.add_option(
            Option('-O3',  bool, 'o3', 'Optimization level 3', action='store_true', default=False)
        )
        self.add_option(
            Option('-ccopt',  str, 'ccopts', 'Additional arguments to pass to llvm-kompile', action='append', default=[])
        )
        self.add_option(
            Option('--enable-search',  bool, 'enable_search', 'Enable search mode on LLVM backend krun', action='store_true', default=False)
        )
        self.add_option(
            Option('--coverage',  bool, 'coverage', 'Enable logging semantics rule coverage measurement', action='store_true', default=False)
        )
        self.add_option(
            Option('--gen-bison-parser',  bool, 'gen_bison_parser', 'Generate standolone Bison parser for program sort.', action='store_true', default=False)
        )
        self.add_option(
            Option('--gen-glr-bison-parser',  bool, 'gen_glr_bison_parser', 'Generate standolone GLR Bison parser for program sort.', action='store_true', default=False)
        )
        self.add_option(
            Option('--bison-lists',  bool, 'bison_lists', 'Disable List{Sort} parsing to make grammar LR(1) for Bison parser.', action='store_true', default=False)
        )
        self.add_option(
            Option('--no-exc-wrap',  bool, 'no_exc_wrap', 'Do not wrap the output on the CLI.', action='store_true', default=False)
        )


class KompileOptions(Options):
    emit_json: bool
    llvm_kompile: bool
    llvm_library: bool
    enable_llvm_debug: bool
    llvm_kompile_type: LLVMKompileType | None
    llvm_kompile_output: Path | None
    llvm_proof_hint_instrumentation: bool
    read_only: bool
    o0: bool
    o1: bool
    o2: bool
    o3: bool
    ccopts: list[str]
    enable_search: bool
    coverage: bool
    gen_bison_parser: bool
    gen_glr_bison_parser: bool
    bison_lists: bool
    no_exc_wrap: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'emit_json': True,
            'llvm_kompile': False,
            'llvm_library': False,
            'enable_llvm_debug': False,
            'llvm_kompile_type': None,
            'llvm_kompile_output': None,
            'llvm_proof_hint_instrumentation': False,
            'read_only': False,
            'o0': False,
            'o1': False,
            'o2': False,
            'o3': False,
            'ccopts': [],
            'enable_search': False,
            'coverage': False,
            'gen_bison_parser': False,
            'gen_glr_bison_parser': False,
            'bison_lists': False,
            'no_exc_wrap': False,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'with-llvm-library': 'llvm_library',
            'read-only-kompiled-directory': 'read_only',
            'ccopt': 'ccopts',
            'O0': 'o0',
            'O1': 'o1',
            'O2': 'o2',
            'O3': 'o3',
        }


class ParallelOptionsGroup(OptionsGroup):
    workers: int

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option(
                '--workers', int, 'workers', 'Number of processes to run in parallel', aliases=['-j'], default=1, toml_name='j'
            )
        )


class ParallelOptions(Options):
    workers: int

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'workers': 1,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return {
            'j': 'workers',
        }


class BugReportOptionsGroup(OptionsGroup):
    bug_report: BugReport | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(Option(
            '--bug-report', bug_report_arg, 'bug_report', 'Generate bug report with given name.', default=None,
        ))


class BugReportOptions(Options):
    bug_report: BugReport | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {'bug_report': None}


class SMTOptionsGroup(OptionsGroup):
    smt_timeout: int
    smt_retry_limit: int
    smt_tactic: str | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            Option('--smt-timeout', int, 'smt_timeout', 'Timeout in ms to use for SMT queries.', default=300)
        )
        self.add_option(
            Option('--smt-retry-limit', int, 'smt_retry_limit', 'Number of times to retry SMT queries with scaling timeouts.', default=10)
        )
        self.add_option(
                Option('--smt-tactic', str, 'smt_tactic', 'Z3 tactic to use with checking satisfiability. Example: (check-sat-using-smt)', default=None)
        )


class SMTOptions(Options):
    smt_timeout: int
    smt_retry_limit: int
    smt_tactic: str | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'smt_timeout': 300,
            'smt_retry_limit': 10,
            'smt_tactic': None,
        }


class ConfigArgs:
    @cached_property
    def config_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--config-file',
            dest='config_file',
            type=file_path,
            default=Path('./pyk.toml'),
            help='Path to Pyk config file.',
        )
        args.add_argument(
            '--config-profile',
            dest='config_profile',
            default='default',
            help='Config profile to be used.',
        )
        return args


class KCLIArgs:
    @cached_property
    def logging_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--verbose', '-v', default=False, action='store_true', help='Verbose output.')
        args.add_argument('--debug', default=False, action='store_true', help='Debug output.')
        return args

    @cached_property
    def warning_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--warnings',
            '-w',
            dest='warnings',
            type=Warnings,
            default=None,
            help='Warnings to print about (no effect on pyk, only subcommands).',
        )
        args.add_argument(
            '--warnings_to_errors',
            '-w2e',
            dest='warnings_to_errors',
            default=False,
            action='store_true',
            help='Turn warnings into errors (no effect on pyk, only subcommands).',
        )
        return args

    @cached_property
    def parallel_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--workers', '-j', default=1, type=int, help='Number of processes to run in parallel.')
        return args

    @cached_property
    def bug_report_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--bug-report',
            type=bug_report_arg,
            help='Generate bug report with given name',
        )
        return args

    @cached_property
    def kompile_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '--output-definition',
            '--definition',
            type=ensure_dir_path,
            dest='definition_dir',
            help='Path to kompile definition to.',
        )
        args.add_argument(
            '--backend',
            type=KompileBackend,
            dest='backend',
            help='K backend to target with compilation.',
        )
        args.add_argument(
            '--type-inference-mode', type=TypeInferenceMode, help='Mode for doing K rule type inference in.'
        )
        args.add_argument(
            '--emit-json',
            dest='emit_json',
            default=True,
            action='store_true',
            help='Emit JSON definition after compilation.',
        )
        args.add_argument(
            '-ccopt',
            dest='ccopts',
            default=[],
            action='append',
            help='Additional arguments to pass to llvm-kompile.',
        )
        args.add_argument(
            '--no-llvm-kompile',
            dest='llvm_kompile',
            default=True,
            action='store_false',
            help='Do not run llvm-kompile process.',
        )
        args.add_argument(
            '--with-llvm-library',
            dest='llvm_library',
            default=False,
            action='store_true',
            help='Make kompile generate a dynamic llvm library.',
        )
        args.add_argument(
            '--enable-llvm-debug',
            dest='enable_llvm_debug',
            default=False,
            action='store_true',
            help='Make kompile generate debug symbols for llvm.',
        )
        args.add_argument('--llvm-kompile-type', type=LLVMKompileType, help='Mode to kompile LLVM backend in.')
        args.add_argument('--llvm-kompile-output', type=Path, help='Location to put kompiled LLVM backend at.')
        args.add_argument(
            '--read-only-kompiled-directory',
            dest='read_only',
            default=False,
            action='store_true',
            help='Generated a kompiled directory that K will not attempt to write to afterwards.',
        )
        args.add_argument('-O0', dest='o0', default=False, action='store_true', help='Optimization level 0.')
        args.add_argument('-O1', dest='o1', default=False, action='store_true', help='Optimization level 1.')
        args.add_argument('-O2', dest='o2', default=False, action='store_true', help='Optimization level 2.')
        args.add_argument('-O3', dest='o3', default=False, action='store_true', help='Optimization level 3.')
        args.add_argument(
            '--enable-search',
            dest='enable_search',
            default=False,
            action='store_true',
            help='Enable search mode on LLVM backend krun.',
        )
        args.add_argument(
            '--coverage',
            dest='coverage',
            default=False,
            action='store_true',
            help='Enable logging semantic rule coverage measurement.',
        )
        args.add_argument(
            '--gen-bison-parser',
            dest='gen_bison_parser',
            default=False,
            action='store_true',
            help='Generate standalone Bison parser for program sort.',
        )
        args.add_argument(
            '--gen-glr-bison-parser',
            dest='gen_glr_bison_parser',
            default=False,
            action='store_true',
            help='Generate standalone GLR Bison parser for program sort.',
        )
        args.add_argument(
            '--bison-lists',
            dest='bison_lists',
            default=False,
            action='store_true',
            help='Disable List{Sort} parsing to make grammar LR(1) for Bison parser.',
        )
        args.add_argument(
            '--llvm-proof-hint-instrumentation',
            dest='llvm_proof_hint_instrumentation',
            default=False,
            action='store_true',
            help='Enable proof hint generation in LLVM backend kompilation.',
        )
        args.add_argument(
            '--no-exc-wrap',
            dest='no_exc_wrap',
            default=False,
            action='store_true',
            help='Do not wrap the output on the CLI.',
        )
        return args

    @cached_property
    def smt_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--smt-timeout', dest='smt_timeout', type=int, help='Timeout in ms to use for SMT queries.')
        args.add_argument(
            '--smt-retry-limit',
            dest='smt_retry_limit',
            type=int,
            help='Number of times to retry SMT queries with scaling timeouts.',
        )
        args.add_argument(
            '--smt-tactic',
            dest='smt_tactic',
            type=str,
            help='Z3 tactic to use when checking satisfiability. Example: (check-sat-using smt)',
        )
        return args

    @cached_property
    def display_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('--minimize', dest='minimize', default=True, action='store_true', help='Minimize output.')
        args.add_argument('--no-minimize', dest='minimize', action='store_false', help='Do not minimize output.')
        return args

    @cached_property
    def definition_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument(
            '-I', type=str, dest='includes', default=[], action='append', help='Directories to lookup K definitions in.'
        )
        args.add_argument('--main-module', type=str, help='Name of the main module.')
        args.add_argument('--syntax-module', type=str, help='Name of the syntax module.')
        args.add_argument(
            '--md-selector',
            type=str,
            help='Code selector expression to use when reading markdown.',
        )
        return args

    @cached_property
    def spec_args(self) -> ArgumentParser:
        args = ArgumentParser(add_help=False)
        args.add_argument('spec_file', type=file_path, help='Path to spec file.')
        args.add_argument('--definition', type=dir_path, dest='definition_dir', help='Path to definition to use.')
        args.add_argument('--spec-module', dest='spec_module', type=str, help='Module with claims to be proven.')
        args.add_argument(
            '--claim',
            type=str,
            dest='claim_labels',
            action='append',
            help='Only prove listed claims, MODULE_NAME.claim-id',
        )
        args.add_argument(
            '--exclude-claim',
            type=str,
            dest='exclude_claim_labels',
            action='append',
            help='Skip listed claims, MODULE_NAME.claim-id',
        )
        args.add_argument(
            '--type-inference-mode',
            dest='type_inference_mode',
            type=TypeInferenceMode,
            help='Mode for doing K rule type inference in.',
        )
        args.add_argument(
            '--save-directory',
            default=None,
            type=ensure_dir_path,
            help='Directory to save proof artifacts at for reuse.',
        )
        args.add_argument(
            '--temp-directory',
            dest='temp_directory',
            default=None,
            type=ensure_dir_path,
            help='Directory to save intermediate temporaries to.',
        )
        return args
