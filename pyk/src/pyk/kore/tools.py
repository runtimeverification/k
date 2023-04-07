from __future__ import annotations

from enum import Enum
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import TYPE_CHECKING

from ..cli_utils import check_dir_path, run_process

if TYPE_CHECKING:
    pass

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


def kore_print(pattern: Pattern, definition_dir: str | Path, output: str | PrintOutput) -> str:
    definition_dir = Path(definition_dir)
    check_dir_path(definition_dir)

    output = PrintOutput(output)

    with NamedTemporaryFile(mode='w') as f:
        pattern.write(f)
        f.write('\n')
        f.flush()

        run_res = run_process(['kore-print', f.name, '--definition', str(definition_dir), '--output', output.value])

    return run_res.stdout.strip()
