from pathlib import Path
from subprocess import CompletedProcess, run
from typing import Any

from ..cli_utils import check_file_path


def kompile(main_file: Path) -> Any:
    check_file_path(main_file)
    _kompile(str(main_file))


def _kompile(main_file: str, *args: str) -> CompletedProcess:
    return run(['kompile', main_file] + list(args), capture_output=True)
