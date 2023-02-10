from pathlib import Path
from typing import Final, Iterator, Tuple

import pytest
from pytest import TempPathFactory

from pyk.konvert import KompiledKore, munge, unmunge
from pyk.kore.syntax import SortApp


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


class KoreFactory:
    _tmp_path_factory: TempPathFactory

    def __init__(self, tmp_path_factory: TempPathFactory):
        self._tmp_path_factory = tmp_path_factory

    def __call__(self, definition_text: str) -> KompiledKore:
        path = self._tmp_path_factory.mktemp('kompiled-defn')
        (path / 'definition.kore').write_text(definition_text)
        (path / 'timestamp').touch()
        return KompiledKore(path)


@pytest.fixture(scope='session')
def kore_factory(tmp_path_factory: TempPathFactory) -> KoreFactory:
    return KoreFactory(tmp_path_factory)


def test_subsort_table(kore_factory: KoreFactory) -> None:
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
    kompiled_kore = kore_factory(definition_text)

    a, b, c, d = (SortApp(name) for name in ['A', 'B', 'C', 'D'])
    expected = {
        b: {a},
        c: {a, b},
        d: {a, b},
    }

    # When
    actual = kompiled_kore._subsort_table

    # Then
    assert actual == expected
