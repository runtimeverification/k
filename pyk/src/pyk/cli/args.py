from __future__ import annotations

import sys
from argparse import ArgumentParser
from functools import cached_property
from pathlib import Path
from typing import IO, TYPE_CHECKING, Any

from ..ktool.kompile import KompileBackend, LLVMKompileType, TypeInferenceMode, Warnings
from .cli import (
    BoolOption,
    BugReportOption,
    DirPathOption,
    EnumOption,
    IntOption,
    Options,
    OptionsGroup,
    StringListOption,
    StringOption,
    WriteFileOption,
)
from .utils import bug_report_arg, dir_path, ensure_dir_path, file_path

if TYPE_CHECKING:
    from collections.abc import Iterable

    from ..utils import BugReport


class LoggingOptionsGroup(OptionsGroup):
    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            BoolOption(name='debug', cmd_line_name='--debug', optional=True, default=False, help_str='Debug output.')
        )
        self.add_option(
            BoolOption(
                name='verbose',
                cmd_line_name='--verbose',
                aliases=['-v'],
                toml_name='v',
                optional=True,
                default=False,
                help_str='Debug output.',
            )
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
            BoolOption(
                name='warnings_to_errors',
                cmd_line_name='--warnings-to-errors',
                aliases=['-w2e'],
                default=False,
                help_str='Turn warnings into errors (no effect on pyk, only subcommands).',
                optional=True,
                toml_name='w2e',
            )
        )
        self.add_option(
            EnumOption(
                name='warnings',
                cmd_line_name='--warnings',
                aliases=['-w'],
                default=False,
                help_str='Warnings to print about (no effect on pyk, only subcommands).',
                optional=True,
                toml_name='w',
                enum_type=Warnings,
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
            WriteFileOption(
                name='output_file',
                cmd_line_name='--output-file',
                default=sys.stdout,
                optional=True,
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
            DirPathOption(name='definition_dir', toml_name='definition', help_str='Path to definition directory.')
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
            BoolOption(
                name='minimize', cmd_line_name='--minimize', optional=True, default=True, help_str='Minimize output.'
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
    main_module: str
    syntax_module: str
    md_selector: str

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            StringListOption(
                name='includes',
                cmd_line_name='-I',
                optional=True,
                default=[],
                help_str='Directories to lookup K definitions in.',
            )
        )
        self.add_option(
            StringOption(
                name='main_module',
                cmd_line_name='--main-module',
                optional=True,
                default=None,
                help_str='Name of the main module.',
            )
        )
        self.add_option(
            StringOption(
                name='syntax_module',
                cmd_line_name='--syntax-module',
                optional=True,
                default=None,
                help_str='Name of the syntax module.',
            )
        )
        self.add_option(
            StringOption(
                name='md_selector',
                cmd_line_name='--md-selector',
                optional=True,
                default='k',
                help_str='Code selector expression to use when reading markdown.',
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


#      @staticmethod
#      def from_option_string() -> dict[str, str]:
#          return {
#              'includes': 'includes',
#          }


class SaveDirOptionsGroup(OptionsGroup):
    save_directory: Path | None
    temp_directory: Path | None

    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            DirPathOption(
                name='save_directory',
                cmd_line_name='--save-directory',
                optional=True,
                default=None,
                help_str='Directory to save proof artifacts at for reuse.',
            )
        )
        self.add_option(
            DirPathOption(
                name='temp_directory',
                cmd_line_name='--temp-directory',
                optional=True,
                default=None,
                help_str='Directory to save proof intermediate temporaries to.',
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
            DirPathOption(
                name='spec_file',
                optional=False,
                help_str='Path to spec file.',
            )
        )
        self.add_option(
            StringOption(
                name='spec_module',
                cmd_line_name='--spec-module',
                optional=True,
                default=None,
                help_str='Module with claims to be proven.',
            )
        )
        self.add_option(
            StringListOption(
                name='claim_labels',
                cmd_line_name='--claim',
                toml_name='claim',
                optional=True,
                default=None,
                help_str='Only prove listed claims, MODULE_NAME.claim-id',
            )
        )
        self.add_option(
            StringListOption(
                name='exclude_claim_labels',
                cmd_line_name='--exclude-claim',
                toml_name='exclude-claim',
                optional=True,
                default=None,
                help_str='Skip listed claims, MODULE_NAME.claim-id',
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
    llvm_kompile_type: LLVMKompileType
    llvm_kompile_output: Path
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
            BoolOption(
                name='emit_json',
                cmd_line_name='--emit-json',
                default=True,
                help_str='Emit JSON definition after compilation.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='llvm_kompile',
                cmd_line_name='--no-llvm-kompile',
                default=False,
                help_str='Do not run llvm-kompile process.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='llvm_library',
                cmd_line_name='--with-llvm-library',
                toml_name='with-llvm-library',
                default=False,
                help_str='Make kompile generate a dynamic llvm library.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='enable_llvm_debug',
                cmd_line_name='--enable-llvm-debug',
                default=False,
                help_str='Make kompile generate debug symbols for llvm.',
                optional=True,
            )
        )
        self.add_option(
            EnumOption(
                enum_type=LLVMKompileType,
                name='llvm_kompile_type',
                cmd_line_name='--llvm-kompile-type',
                default=None,
                help_str='Mode to kompile LLVM backend in.',
            )
        )
        self.add_option(
            DirPathOption(
                name='llvm_kompile_output',
                cmd_line_name='--llvm-kompile-output',
                default=None,
                help_str='Location to put kompiled LLVM backend at.',
            )
        )
        self.add_option(
            BoolOption(
                name='llvm_proof_hint_instrumentation',
                cmd_line_name='--llvm-proof-hint-instrumentation',
                default=False,
                help_str='Enable proof hint generation in LLVM backend kompilation.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='read_only',
                cmd_line_name='--read-only-kompiled-directory',
                toml_name='read-only-kompiled-directory',
                default=False,
                help_str='Generate a kompiled directory that K will not attempt to write to afterwards.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='o0',
                cmd_line_name='-O0',
                toml_name='O0',
                default=False,
                help_str='Optimization level 0.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='o1',
                cmd_line_name='-O1',
                toml_name='O1',
                default=False,
                help_str='Optimization level 1.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='o2',
                cmd_line_name='-O2',
                toml_name='O2',
                default=False,
                help_str='Optimization level 2.',
                optional=True,
            )
        )
        self.add_option(
            BoolOption(
                name='o3',
                cmd_line_name='-O3',
                toml_name='O3',
                default=False,
                help_str='Optimization level 3.',
                optional=True,
            )
        )
        self.add_option(
            StringListOption(
                name='ccopts',
                cmd_line_name='-ccopt',
                optional=True,
                default=[],
                help_str='Additional arguments to pass to llvm-kompile',
            )
        )
        self.add_option(
            BoolOption(
                name='enable_search',
                cmd_line_name='--enable-search',
                optional=True,
                default=False,
                help_str='Enable search mode on LLVM backend krun.',
            )
        )
        self.add_option(
            BoolOption(
                name='coverage',
                cmd_line_name='--coverage',
                optional=True,
                default=False,
                help_str='Enable logging semantic rule coverage measurement.',
            )
        )
        self.add_option(
            BoolOption(
                name='gen_bison_parser',
                cmd_line_name='--gen-bison-parser',
                optional=True,
                default=False,
                help_str='Generate standalone Bison parser for program sort.',
            )
        )
        self.add_option(
            BoolOption(
                name='gen_glr_bison_parser',
                cmd_line_name='--gen-glr-bison-parser',
                optional=True,
                default=False,
                help_str='Generate standalone GLR Bison parser for program sort.',
            )
        )
        self.add_option(
            BoolOption(
                name='bison_lists',
                cmd_line_name='--bison-lists',
                optional=True,
                default=False,
                help_str='Disable List{Sort} parsing to make grammar LR(1) for Bison parser.',
            )
        )
        self.add_option(
            BoolOption(
                name='no_exc_wrap',
                cmd_line_name='--no-exc-wrap',
                optional=True,
                default=False,
                help_str='Do not wrap the output on the CLI.',
            )
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
    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            IntOption(
                name='workers',
                aliases=['-j'],
                cmd_line_name='--workers',
                toml_name='j',
                default=1,
                help_str='Number of processes to run in parallel',
                optional=True,
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
    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            BugReportOption(
                name='bug_report',
                cmd_line_name='--bug-report',
                default=None,
                help_str='Generate bug report with given name.',
                optional=True,
            )
        )


class BugReportOptions(Options):
    bug_report: BugReport | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {'bug_report': None}


class SMTOptionsGroup(OptionsGroup):
    def __init__(self) -> None:
        super().__init__()
        self.add_option(
            IntOption(
                name='smt_timeout',
                cmd_line_name='--smt-timeout',
                default=300,
                help_str='Timeout in ms to use for SMT queries.',
                optional=True,
            )
        )
        self.add_option(
            IntOption(
                name='smt_retry_limit',
                cmd_line_name='--smt-retry-limit',
                default=10,
                help_str='Number of times to retry SMT queries with scaling timeouts.',
                optional=True,
            )
        )
        self.add_option(
            StringOption(
                name='smt_tactic',
                cmd_line_name='--smt-tactic',
                default=None,
                help_str='Z3 tactic to use when checking satisfiability. Example: (check-sat-using-smt)',
                optional=True,
            )
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
