from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from _kllvm.parser import Parser  # type: ignore

from ..cli.utils import check_file_path

if TYPE_CHECKING:
    from .ast import Pattern


def parse_text(text: str) -> Pattern:
    parser = Parser.from_string(text)
    return parser.pattern()


def parse_file(path: str | Path) -> Pattern:
    path = Path(path)
    check_file_path(path)
    parser = Parser(str(path))
    return parser.pattern()
