from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.ast import CompositeSort, Symbol, Variable

if TYPE_CHECKING:
    from typing import Final

s1 = Symbol("Lbl'Plus")
s2 = Symbol("Lbl'Plus")
s2.add_formal_argument(CompositeSort('A'))

STR_TEST_DATA: Final = (
    (s1, "Lbl'Plus{}"),
    (s2, "Lbl'Plus{A{}}"),
)


@pytest.mark.parametrize('symbol,expected', STR_TEST_DATA, ids=[expected for _, expected in STR_TEST_DATA])
def test_str(symbol: Symbol, expected: str) -> None:
    # When
    actual = str(symbol)

    # Then
    assert actual == expected


def test_equal() -> None:
    # Given
    a1 = Symbol('A')
    a2 = Symbol('A')
    b = Symbol('B')

    # Then
    assert a1 is not a2
    assert a1 == a2
    assert a1 != b


def test_variable() -> None:
    # When
    a = Variable('A')

    # Then
    assert a.name == 'A'
    assert str(a) == 'A'
