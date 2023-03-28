from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kllvm.parser import Parser, read_pattern

if TYPE_CHECKING:
    from pathlib import Path


def test_read_pattern(tmp_path: Path) -> None:
    # Given
    kore_text = 'A{}(B{}(),C{}())'
    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)

    # When
    actual = read_pattern(kore_file)

    # Then
    assert str(actual) == kore_text


def test_parser_from_file(tmp_path: Path) -> None:
    # Given
    kore_text = 'A{}(B{}(),C{}())'
    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)
    parser = Parser(str(kore_file))

    # When
    actual = parser.pattern()

    # Then
    assert str(actual) == kore_text


def test_parser_from_string() -> None:
    # Given
    kore_text = 'A{}(X : S,Y : Z,Int{}())'
    parser = Parser.from_string(kore_text)

    # When
    actual = parser.pattern()

    # Then
    assert str(actual) == kore_text
