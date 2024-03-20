from __future__ import annotations

import sys
from argparse import ArgumentParser
from functools import cached_property
from pathlib import Path
from typing import IO, TYPE_CHECKING, Any

from ..ktool.kompile import KompileBackend, LLVMKompileType, TypeInferenceMode, Warnings
from .cli import Options
from .utils import bug_report_arg, ensure_dir_path, file_path

if TYPE_CHECKING:
    from ..utils import BugReport


class LoggingOptions(Options):
    debug: bool
    verbose: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'verbose': False,
            'debug': False,
        }


class WarningOptions(Options):
    warnings: Warnings | None
    warning_to_error: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'warnings': None,
            'warning_to_error': False,
        }


class OutputFileOptions(Options):
    output_file: IO[Any]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output_file': sys.stdout,
        }


class DefinitionOptions(Options):
    definition_dir: Path


class DisplayOptions(Options):
    minimize: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'minimize': True,
        }


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


class SaveDirOptions(Options):
    save_directory: Path | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'save_directory': None,
        }


class SpecOptions(SaveDirOptions):
    spec_file: Path
    claim_labels: list[str] | None
    exclude_claim_labels: list[str]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'claim_labels': None,
            'exclude_claim_labels': [],
        }


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
        }


class ParallelOptions(Options):
    workers: int

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'workers': 1,
        }


class BugReportOptions(Options):
    bug_report: BugReport | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {'bug_report': None}


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
            '-w2e',
            dest='warning_to_error',
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
        args.add_argument('--save-directory', type=ensure_dir_path, help='Path to where CFGs are stored.')
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
        return args
