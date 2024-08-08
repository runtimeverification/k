from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.ast import CompositePattern, CompositeSort, Pattern, StringPattern, VariablePattern

if TYPE_CHECKING:
    from pathlib import Path


@pytest.mark.parametrize(
    'kore_text',
    (
        'A{}(B{}(),C{}())',
        '"string pattern"',
        'XYZ : ABC',
    ),
)
def test_file_load(tmp_path: Path, kore_text: str) -> None:
    # Given
    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)

    # When
    actual = Pattern(str(kore_file))

    # Then
    assert str(actual) == kore_text


def test_composite() -> None:
    # Given
    pattern = CompositePattern('F')
    pattern.add_argument(CompositePattern('A'))
    pattern.add_argument(VariablePattern('X', CompositeSort('S')))

    # When
    actual = pattern.substitute({'X': CompositePattern('B')})

    # Then
    assert str(actual) == 'F{}(A{}(),B{}())'


def test_string() -> None:
    # Given
    pattern = StringPattern('abc')

    # Then
    assert str(pattern) == '"abc"'
    assert pattern.contents.decode('latin-1') == 'abc'


def test_variable() -> None:
    # Given
    pattern = VariablePattern('X', CompositeSort('S'))

    # When
    actual = pattern.substitute({'X': CompositePattern('A')})

    # Then
    assert str(actual) == 'A{}()'
