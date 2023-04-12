from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.ast import CompositeSort, SortVariable

if TYPE_CHECKING:
    from pyk.kllvm.ast import Sort


@pytest.mark.parametrize(
    'sort,expected',
    (
        (CompositeSort('A'), True),
        (SortVariable('B'), False),
    ),
)
def test_is_concrete(sort: Sort, expected: bool) -> None:
    # When
    actual = sort.is_concrete

    # Then
    assert actual == expected


@pytest.mark.parametrize('name', ('A', 'SortInt', ''))
def test_name(name: str) -> None:
    # When
    sort = CompositeSort(name)

    # Then
    assert sort.name == name


@pytest.mark.parametrize(
    'sort,expected',
    (
        (CompositeSort('A'), 'A{}'),
        (SortVariable('B'), 'B'),
    ),
)
def test_str(sort: Sort, expected: str) -> None:
    # When
    actual = str(sort)

    # Then
    assert actual == expected


def test_add_argument() -> None:
    # Given
    f = CompositeSort('F')
    a = CompositeSort('A')
    b = SortVariable('B')

    # When
    f.add_argument(a)
    f.add_argument(b)

    # Then
    assert str(f) == 'F{A{},B}'


def test_substitution_1() -> None:
    # Given
    x = SortVariable('X')
    a = CompositeSort('A')
    expected = a

    # When
    actual = a.substitute({x: a})

    # Then
    assert actual == expected


def test_substitution_2() -> None:
    x = SortVariable('X')
    y = SortVariable('Y')
    a = CompositeSort('A')
    b = CompositeSort('B')
    c = CompositeSort('C')

    original = CompositeSort('F')
    g1 = CompositeSort('G')
    g1.add_argument(x)
    g1.add_argument(x)
    g1.add_argument(b)
    g1.add_argument(y)
    original.add_argument(g1)

    assert str(original) == 'F{G{X,X,B{},Y}}'
    assert not original.is_concrete

    expected = CompositeSort('F')
    g2 = CompositeSort('G')
    g2.add_argument(a)
    g2.add_argument(a)
    g2.add_argument(b)
    g2.add_argument(c)
    expected.add_argument(g2)

    assert str(expected), 'F{G{A{},A{},B{},C{}}}'
    assert expected.is_concrete

    # When
    actual = original.substitute({x: a, y: c})

    # Then
    assert actual == expected


def test_equality() -> None:
    # Given
    a1 = CompositeSort('A')
    a2 = CompositeSort('A')
    b1 = SortVariable('B')
    b2 = SortVariable('B')

    # Then
    assert a1 is not a2
    assert a1 == a2
    assert b1 is not b2
    assert b1 == b2
    assert a1 != b1
    assert a2 != b2
