from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pykframework.kast import _ast_to_kast
from pykframework.kast.att import EMPTY_ATT, KAtt
from pykframework.kast.outer import KDefinition, KFlatModule, KImport, KRequire
from pykframework.kast.outer_syntax import Att, Definition, Import, Module, Require

if TYPE_CHECKING:
    from typing import Final

    from pykframework.kast.att import KAst
    from pykframework.kast.outer_syntax import AST


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
