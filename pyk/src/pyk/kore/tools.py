from __future__ import annotations

from enum import Enum
from pathlib import Path
from tempfile import NamedTemporaryFile

from ..cli.utils import check_dir_path
from ..utils import run_process
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


def kore_print(pattern: str | Pattern, definition_dir: str | Path, output: str | PrintOutput) -> str:
    definition_dir = Path(definition_dir)
    check_dir_path(definition_dir)

    output = PrintOutput(output)

    if type(pattern) is str and output == PrintOutput.KORE:
        return pattern

    with NamedTemporaryFile(mode='w') as f:
        if isinstance(pattern, Pattern):
            pattern.write(f)
            f.write('\n')
        elif type(pattern) is str:
            f.write(pattern)
        else:
            raise TypeError(f'Unexpected type, expected [str | Pattern], got: {type(pattern)}')
        f.flush()

        run_res = run_process(['kore-print', f.name, '--definition', str(definition_dir), '--output', output.value])

    return run_res.stdout.strip()
