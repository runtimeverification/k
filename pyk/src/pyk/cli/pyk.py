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
        case 'kompile':
            return KompileCommandOptions(args)
        case 'run':
            return RunOptions(args)
        case _:
            raise ValueError(f'Unrecognized command: {command}')


class PrintInput(Enum):
    KORE_JSON = 'kore-json'
    KAST_JSON = 'kast-json'


class JsonToKoreOptions(LoggingOptions): ...


class KoreToJsonOptions(LoggingOptions): ...


class CoverageOptions(DefinitionOptions, OutputFileOptions, LoggingOptions):
    coverage_file: IO[Any]


class GraphImportsOptions(DefinitionOptions, LoggingOptions): ...


class RPCKastOptions(OutputFileOptions, LoggingOptions):
    reference_request_file: IO[Any]
    response_file: IO[Any]


class RPCPrintOptions(DefinitionOptions, OutputFileOptions, LoggingOptions):
    input_file: IO[Any]


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


class ProveOptions(LoggingOptions, SpecOptions, SaveDirOptions):
    definition_dir: Path | None
    type_inference_mode: TypeInferenceMode | None
    failure_info: bool
    max_depth: int | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'definition_dir': None,
            'type_inference_mode': None,
            'failure_info': False,
            'max_depth': None,
        }


class RunOptions(LoggingOptions):
    pgm_file: str
    definition_dir: Path | None

    @staticmethod
    def default() -> dict[str, Any]:
        return {
            'definition_dir': None,
        }
