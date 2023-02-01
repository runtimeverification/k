from pathlib import Path
from typing import Final, Iterator, Tuple

import pytest

from pyk.konvert import _subsort_dict, munge, unmunge
from pyk.kore.syntax import Attr, Axiom, Definition, Module, Sort, SortApp, SortVar, Top


def test_subsort_dict() -> None:
    def sort_axiom(subsort: Sort, supersort: Sort) -> Axiom:
        r = SortVar('R')
        return Axiom((r,), Top(r), attrs=(Attr('subsort', (subsort, supersort)),))

    a, b, c, d = (SortApp(name) for name in ['a', 'b', 'c', 'd'])

    # When
    definition = Definition(
        (
            Module(
                'MODULE-1',
                (sort_axiom(a, d), sort_axiom(b, d)),
            ),
            Module('MODULE-2', (sort_axiom(b, c),)),
        )
    )
    expected = {
        c: {b},
        d: {a, b},
    }

    # When
    actual = _subsort_dict(definition)

    # Then
    assert actual == expected


def munge_test_data_reader() -> Iterator[Tuple[str, str]]:
    test_data_file = Path(__file__).parent / 'test-data/munge-tests'
    with open(test_data_file, 'r') as f:
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
