from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from _kllvm.parser import Parser  # type: ignore

from ..cli.utils import check_file_path

if TYPE_CHECKING:
    from .ast import Definition, Pattern, Sort


def parse_pattern(text: str) -> Pattern:
    return Parser.from_string(text).pattern()


def parse_sort(text: str) -> Sort:
    return Parser.from_string(text).sort()


def parse_definition(text: str) -> Definition:
    return Parser.from_string(text).definition()


def parse_pattern_file(path: str | Path) -> Pattern:
    return _parser_from_path(path).pattern()


def parse_sort_file(path: str | Path) -> Pattern:
    return _parser_from_path(path).sort()


def parse_definition_file(path: str | Path) -> Definition:
    return _parser_from_path(path).definition()


def _parser_from_path(path: str | Path) -> Parser:
    path = Path(path)
    check_file_path(path)
    return Parser(str(path))
