from .native import _kllvm  # isort: skip  # noqa: F401

from pathlib import Path
from typing import Union

from _kllvm.parser import Parser  # type: ignore

from ..cli_utils import check_file_path
from .ast import Pattern


def read_pattern(path: Union[str, Path]) -> Pattern:
    path = Path(path)
    check_file_path(path)
    parser = Parser(str(path))
    return parser.pattern()
