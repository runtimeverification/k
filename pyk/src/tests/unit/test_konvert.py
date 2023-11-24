from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.konvert import munge, unmunge
from pyk.kore.kompiled import KoreSortTable
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import SortApp

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Final


def munge_test_data_reader() -> Iterator[tuple[str, str]]:
    test_data_file = Path(__file__).parent / 'test-data/munge-tests'
    with open(test_data_file) as f:
        while True:
            try:
                label = next(f)
                symbol = next(f)
            except StopIteration:
                raise AssertionError('Malformed test data') from None

            yield label.rstrip('\n'), symbol.rstrip('\n')

            try:
                next(f)
            except StopIteration:
                return


MUNGE_TEST_DATA: Final = tuple(munge_test_data_reader())


@pytest.mark.parametrize('label,expected', MUNGE_TEST_DATA, ids=[label for label, _ in MUNGE_TEST_DATA])
def test_munge(label: str, expected: str) -> None:
    # When
    actual = munge(label)

    # Then
    assert actual == expected


@pytest.mark.parametrize('expected,symbol', MUNGE_TEST_DATA, ids=[symbol for _, symbol in MUNGE_TEST_DATA])
def test_unmunge(symbol: str, expected: str) -> None:
    # When
    actual = unmunge(symbol)

    # Then
    assert actual == expected


def test_kore_sort_table() -> None:
    # When
    definition_text = r"""
        []
        module MODULE-1
            axiom{R} \top{R}() [subsort{A{}, B{}}()]
            axiom{R} \top{R}() [subsort{B{}, C{}}()]
        endmodule []
        module MODULE-2
            axiom{R} \top{R}() [subsort{B{}, D{}}()]
        endmodule []
    """
    definition = KoreParser(definition_text).definition()
    sort_table = KoreSortTable.for_definition(definition)

    a, b, c, d = (SortApp(name) for name in ['A', 'B', 'C', 'D'])
    expected = {
        b: {a},
        c: {a, b},
        d: {a, b},
    }

    # When
    actual = sort_table._subsort_table

    # Then
    assert actual == expected
