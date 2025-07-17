from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pathlib import Path


def test_parse_pattern_file(load_kllvm: None, tmp_path: Path) -> None:
    from pyk.kllvm import parser

    # Given
    kore_text = 'A{}(B{}(),C{}())'
    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)

    # When
    actual = parser.parse_pattern_file(kore_file)

    # Then
    assert str(actual) == kore_text


def test_parse_pattern(load_kllvm: None) -> None:
    from pyk.kllvm import parser

    # Given
    kore_text = 'A{}(X : S,Y : Z,Int{}())'

    # When
    actual = parser.parse_pattern(kore_text)

    # Then
    assert str(actual) == kore_text


def test_parse_sort_file(load_kllvm: None, tmp_path: Path) -> None:
    from pyk.kllvm import parser

    # Given
    kore_text = 'Foo{Bar,Baz}'
    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)

    # When
    actual = parser.parse_sort_file(kore_file)

    # Then
    assert str(actual) == kore_text


def test_parse_sort(load_kllvm: None) -> None:
    from pyk.kllvm import parser

    # Given
    kore_text = 'Foo{Bar,Baz}'

    # When
    actual = parser.parse_sort(kore_text)

    # Then
    assert str(actual) == kore_text


def test_parse_definition_file(load_kllvm: None, tmp_path: Path) -> None:
    from pyk.kllvm import parser

    # Given
    # fmt: off
    kore_text = (
        '[]\n'
        '\n'
        'module FOO\n'
        '  axiom {S}A{}(B{}(),C{}()) [group{}("foo")]\n'
        'endmodule\n'
        '[concrete{}()]\n'
    )
    # fmt: on

    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)

    # When
    actual = parser.parse_definition_file(kore_file)

    # Then
    assert str(actual) == kore_text


def test_parse_definition(load_kllvm: None) -> None:
    from pyk.kllvm import parser

    # Given
    kore_text = (
        '[]\n'
        '\n'
        'module FOO\n'
        '  axiom {S}A{}(X : S,Y : Z,Int{}()) [group{}("foo")]\n'
        'endmodule\n'
        '[concrete{}()]\n'
    )

    # When
    actual = parser.parse_definition(kore_text)

    # Then
    assert str(actual) == kore_text
