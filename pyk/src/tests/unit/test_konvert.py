from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast.att import EMPTY_ATT, KAtt
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire
from pyk.kast.outer_syntax import Att, Definition, Import, Module, Require
from pyk.konvert import _ast_to_kast, munge, unmunge

if TYPE_CHECKING:
    from collections.abc import Iterator
    from typing import Final

    from pyk.kast.att import KAst
    from pyk.kast.outer_syntax import AST


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


AST_TO_KAST_TEST_DATA: Final = [
    (Import('A'), KImport('A')),
    (Import('B', public=False), KImport('B', False)),
    (Require('domains.md'), KRequire('domains.md')),
    (Module('MAIN'), KFlatModule('MAIN')),
    (Att([]), EMPTY_ATT),
    (Att([('concrete', '')]), KAtt.from_dict({'att': {'concrete': ''}})),
]


@pytest.mark.parametrize('ast,expected', AST_TO_KAST_TEST_DATA, ids=[id for id, _ in enumerate(AST_TO_KAST_TEST_DATA)])
def test_ast_to_kast(ast: AST, expected: KAst) -> None:
    # When
    actual = _ast_to_kast(ast)

    # Then
    assert actual == expected


AST_TO_KAST_ARGS_TEST_DATA: Final = [
    (Definition((Module('MAIN'),), ()), KDefinition('MAIN', (KFlatModule('MAIN'),)), {'main_module': 'MAIN'}),
]


@pytest.mark.parametrize(
    'ast,expected,kwargs',
    AST_TO_KAST_ARGS_TEST_DATA,
    ids=[id for id, _ in enumerate(AST_TO_KAST_ARGS_TEST_DATA)],
)
def test_ast_to_kast_args(ast: AST, expected: KAst, kwargs: dict) -> None:
    # When
    actual = _ast_to_kast(ast, **kwargs)

    # Then
    assert actual == expected
