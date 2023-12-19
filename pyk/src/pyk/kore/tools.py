from __future__ import annotations

from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from ..utils import run_process

if TYPE_CHECKING:
    from .syntax import Pattern


class PrintOutput(Enum):
    PRETTY = 'pretty'
    PROGRAM = 'program'
    KAST = 'kast'
    BINARY = 'binary'
    JSON = 'json'
    LATEX = 'latex'
    KORE = 'kore'
    NONE = 'none'


def kore_print(
    pattern: str | Pattern,
    *,
    definition_dir: str | Path | None = None,
    output_file: str | Path | None = None,
    output: str | PrintOutput | None = None,
    color: bool | None = None,
) -> str:
    input = pattern if isinstance(pattern, str) else pattern.text
    if output is not None:
        output = PrintOutput(output)
    if output is PrintOutput.KORE:
        return input
    return _kore_print(
        '/dev/stdin',
        definition_dir=definition_dir,
        output_file=output_file,
        output=output,
        color=color,
        input=input,
    )


def _kore_print(
    input_file: str | Path,
    *,
    definition_dir: str | Path | None = None,
    output_file: str | Path | None = None,
    output: str | PrintOutput | None = None,
    color: bool | None = None,
    # ---
    input: str | None,
) -> str:
    args = ['kore-print']

    input_file = Path(input_file)
    if not input_file.is_char_device():
        check_file_path(input_file)
    args += [str(input_file)]

    if definition_dir is not None:
        definition_dir = Path(definition_dir)
        check_dir_path(definition_dir)
        args += ['--definition', str(definition_dir)]

    if output_file is not None:
        output_file = Path(output_file)
        check_file_path(output_file)
        args += ['--output_file', str(output_file)]

    if output is not None:
        output = PrintOutput(output)
        args += ['--output', output.value]

    if color is not None:
        args += ['--color', 'on' if color else 'off']

    run_res = run_process(args, input=input)
    return run_res.stdout.strip()
