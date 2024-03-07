from __future__ import annotations

import sys
from argparse import FileType
from typing import IO, TYPE_CHECKING, Any

from pyk.utils import ensure_dir_path

from .cli import Options
from .utils import bug_report_arg, dir_path, file_path

if TYPE_CHECKING:
    from argparse import ArgumentParser
    from pathlib import Path
    from typing import TypeVar

    from ..utils import BugReport

    T = TypeVar('T')


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
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output.')
        parser.add_argument('--debug', action='store_true', help='Debug output.')


class OutputFileOptions(Options):
    output_file: IO[Any]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'output_file': sys.stdout,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('--output-file', type=FileType('w'))


class DefinitionOptions(Options):
    definition_dir: Path

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('definition_dir', type=dir_path, help='Path to definition directory.')


class DisplayOptions(Options):
    minimize: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'minimize': True,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('--minimize', dest='minimize', action='store_true', help='Minimize output.')
        parser.add_argument('--no-minimize', dest='minimize', action='store_false', help='Do not minimize output.')


class KDefinitionOptions(Options):
    includes: list[str]
    main_module: str | None
    syntax_module: str | None
    spec_module: str | None
    definition_dir: Path | None
    md_selector: str

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'spec_module': None,
            'main_module': None,
            'syntax_module': None,
            'definition_dir': None,
            'md_selector': 'k',
            'includes': [],
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            '-I', type=str, dest='includes', action='append', help='Directories to lookup K definitions in.'
        )
        parser.add_argument('--main-module', type=str, help='Name of the main module.')
        parser.add_argument('--syntax-module', type=str, help='Name of the syntax module.')
        parser.add_argument('--spec-module', type=str, help='Name of the spec module.')
        parser.add_argument('--definition', type=dir_path, dest='definition_dir', help='Path to definition to use.')
        parser.add_argument(
            '--md-selector',
            type=str,
            help='Code selector expression to use when reading markdown.',
        )


class SaveDirOptions(Options):
    save_directory: Path | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'save_directory': None,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('--save-directory', type=ensure_dir_path, help='Path to where CFGs are stored.')


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

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('spec_file', type=file_path, help='Path to spec file.')
        parser.add_argument(
            '--claim',
            type=str,
            dest='claim_labels',
            action='append',
            help='Only prove listed claims, MODULE_NAME.claim-id',
        )
        parser.add_argument(
            '--exclude-claim',
            type=str,
            dest='exclude_claim_labels',
            action='append',
            help='Skip listed claims, MODULE_NAME.claim-id',
        )


class KompileOptions(Options):
    emit_json: bool
    ccopts: list[str]
    llvm_kompile: bool
    llvm_library: bool
    enable_llvm_debug: bool
    read_only: bool
    o0: bool
    o1: bool
    o2: bool
    o3: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'emit_json': True,
            'llvm_kompile': False,
            'llvm_library': False,
            'enable_llvm_debug': False,
            'read_only': False,
            'o0': False,
            'o1': False,
            'o2': False,
            'o3': False,
            'ccopts': [],
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            '--emit-json',
            dest='emit_json',
            action='store_true',
            help='Emit JSON definition after compilation.',
        )
        parser.add_argument(
            '--no-emit-json', dest='emit_json', action='store_false', help='Do not JSON definition after compilation.'
        )
        parser.add_argument(
            '-ccopt',
            dest='ccopts',
            action='append',
            help='Additional arguments to pass to llvm-kompile.',
        )
        parser.add_argument(
            '--no-llvm-kompile',
            dest='llvm_kompile',
            action='store_false',
            help='Do not run llvm-kompile process.',
        )
        parser.add_argument(
            '--with-llvm-library',
            dest='llvm_library',
            action='store_true',
            help='Make kompile generate a dynamic llvm library.',
        )
        parser.add_argument(
            '--enable-llvm-debug',
            dest='enable_llvm_debug',
            action='store_true',
            help='Make kompile generate debug symbols for llvm.',
        )
        parser.add_argument(
            '--read-only-kompiled-directory',
            dest='read_only',
            action='store_true',
            help='Generated a kompiled directory that K will not attempt to write to afterwards.',
        )
        parser.add_argument('-O0', dest='o0', action='store_true', help='Optimization level 0.')
        parser.add_argument('-O1', dest='o1', action='store_true', help='Optimization level 1.')
        parser.add_argument('-O2', dest='o2', action='store_true', help='Optimization level 2.')
        parser.add_argument('-O3', dest='o3', action='store_true', help='Optimization level 3.')


class ParallelOptions(Options):
    workers: int

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'workers': 1,
        }

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('--workers', '-j', type=int, help='Number of processes to run in parallel.')


class BugReportOptions(Options):
    bug_report: BugReport | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {'bug_report': None}

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument(
            '--bug-report',
            type=bug_report_arg,
            help='Generate bug report with given name',
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

    @staticmethod
    def update_args(parser: ArgumentParser) -> None:
        parser.add_argument('--smt-timeout', dest='smt_timeout', type=int, help='Timeout in ms to use for SMT queries.')
        parser.add_argument(
            '--smt-retry-limit',
            dest='smt_retry_limit',
            type=int,
            help='Number of times to retry SMT queries with scaling timeouts.',
        )
        parser.add_argument(
            '--smt-tactic',
            dest='smt_tactic',
            type=str,
            help='Z3 tactic to use when checking satisfiability. Example: (check-sat-using smt)',
        )
