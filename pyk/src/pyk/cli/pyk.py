from __future__ import annotations

from enum import Enum
from typing import IO, TYPE_CHECKING, Any

from ..ktool.kompile import KompileBackend
from .args import (
    DefinitionOptions,
    DisplayOptions,
    KDefinitionOptions,
    KompileOptions,
    LoggingOptions,
    OutputFileOptions,
    SaveDirOptions,
    SpecOptions,
    WarningOptions,
)

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path

    from pyk.ktool import TypeInferenceMode


def generate_options(args: dict[str, Any]) -> LoggingOptions:
    command = args['command']
    match command:
        case 'json-to-kore':
            return JsonToKoreOptions(args)
        case 'kore-to-json':
            return KoreToJsonOptions(args)
        case 'coverage':
            return CoverageOptions(args)
        case 'graph-imports':
            return GraphImportsOptions(args)
        case 'rpc-kast':
            return RPCKastOptions(args)
        case 'rpc-print':
            return RPCPrintOptions(args)
        case 'print':
            return PrintOptions(args)
        case 'prove-legacy':
            return ProveLegacyOptions(args)
        case 'prove':
            return ProveOptions(args)
        case 'show':
            return ProveOptions(args)
        case 'kompile':
            return KompileCommandOptions(args)
        case 'run':
            return RunOptions(args)
        case _:
            raise ValueError(f'Unrecognized command: {command}')


def get_option_string_destination(command: str, option_string: str) -> str:
    option_string_destinations = {}
    match command:
        case 'json-to-kore':
            option_string_destinations = JsonToKoreOptions.from_option_string()
        case 'kore-to-json':
            option_string_destinations = KoreToJsonOptions.from_option_string()
        case 'coverage':
            option_string_destinations = CoverageOptions.from_option_string()
        case 'graph-imports':
            option_string_destinations = GraphImportsOptions.from_option_string()
        case 'rpc-kast':
            option_string_destinations = RPCKastOptions.from_option_string()
        case 'rpc-print':
            option_string_destinations = RPCPrintOptions.from_option_string()
        case 'print':
            option_string_destinations = PrintOptions.from_option_string()
        case 'prove-legacy':
            option_string_destinations = ProveLegacyOptions.from_option_string()
        case 'prove':
            option_string_destinations = ProveOptions.from_option_string()
        case 'kompile':
            option_string_destinations = KompileCommandOptions.from_option_string()
        case 'run':
            option_string_destinations = RunOptions.from_option_string()

    if option_string in option_string_destinations:
        return option_string_destinations[option_string]
    else:
        return option_string.replace('-', '_')


class PrintInput(Enum):
    KORE_JSON = 'kore-json'
    KAST_JSON = 'kast-json'


class JsonToKoreOptions(LoggingOptions): ...


class KoreToJsonOptions(LoggingOptions): ...


class CoverageOptions(DefinitionOptions, OutputFileOptions, LoggingOptions):
    coverage_file: IO[Any]

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return (
            DefinitionOptions.from_option_string()
            | OutputFileOptions.from_option_string()
            | LoggingOptions.from_option_string()
        )


class GraphImportsOptions(DefinitionOptions, LoggingOptions):
    @staticmethod
    def from_option_string() -> dict[str, str]:
        return DefinitionOptions.from_option_string() | LoggingOptions.from_option_string()


class RPCKastOptions(OutputFileOptions, LoggingOptions):
    reference_request_file: IO[Any]
    response_file: IO[Any]

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return OutputFileOptions.from_option_string() | LoggingOptions.from_option_string()


class RPCPrintOptions(DefinitionOptions, OutputFileOptions, LoggingOptions):
    input_file: IO[Any]

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return (
            DefinitionOptions.from_option_string()
            | OutputFileOptions.from_option_string()
            | LoggingOptions.from_option_string()
        )


class PrintOptions(DefinitionOptions, OutputFileOptions, DisplayOptions, LoggingOptions):
    term: IO[Any]
    input: PrintInput
    minimize: bool
    omit_labels: str | None
    keep_cells: str | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'input': PrintInput.KAST_JSON,
            'omit_labels': None,
            'keep_cells': None,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return (
            DefinitionOptions.from_option_string()
            | OutputFileOptions.from_option_string()
            | DisplayOptions.from_option_string()
            | LoggingOptions.from_option_string()
        )


class ProveLegacyOptions(DefinitionOptions, OutputFileOptions, LoggingOptions):
    main_file: Path
    spec_file: Path
    spec_module: str
    k_args: Iterable[str]

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'k_args': [],
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return (
            DefinitionOptions.from_option_string()
            | OutputFileOptions.from_option_string()
            | LoggingOptions.from_option_string()
            | {'kArgs': 'k_args'}
        )


class KompileCommandOptions(LoggingOptions, WarningOptions, KDefinitionOptions, KompileOptions):
    definition_dir: Path | None
    main_file: str
    backend: KompileBackend
    type_inference_mode: TypeInferenceMode | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'definition_dir': None,
            'backend': KompileBackend.LLVM,
            'type_inference_mode': None,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return (
            KDefinitionOptions.from_option_string()
            | KompileOptions.from_option_string()
            | LoggingOptions.from_option_string()
            | {'definition': 'definition_dir'}
        )


class ProveOptions(LoggingOptions, SpecOptions, SaveDirOptions):
    definition_dir: Path | None
    type_inference_mode: TypeInferenceMode | None
    failure_info: bool
    max_depth: int | None
    max_iterations: int | None
    show_kcfg: bool

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'definition_dir': None,
            'type_inference_mode': None,
            'failure_info': False,
            'max_depth': None,
            'max_iterations': None,
            'show_kcfg': False,
        }

    @staticmethod
    def from_option_string() -> dict[str, str]:
        return (
            KDefinitionOptions.from_option_string()
            | KompileOptions.from_option_string()
            | LoggingOptions.from_option_string()
            | {'definition': 'definition_dir'}
        )


class RunOptions(LoggingOptions):
    pgm_file: str
    definition_dir: Path | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'definition_dir': None,
        }
