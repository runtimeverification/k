from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable
from pyk.kast.manip import inline_cell_maps, remove_attrs
from pyk.kast.pretty import assoc_with_unit
from pyk.prelude.collections import set_of
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kbool import andBool
from pyk.prelude.kint import INT, intToken, leInt, ltInt
from pyk.prelude.utils import token
from pyk.testing import KPrintTest

from .utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.kast import KInner
    from pyk.ktool.kprint import KPrint, SymbolTable


PARSE_TOKEN_TEST_DATA: Final = (
    ('int-token', False, KToken('3', 'Int'), intToken(3)),
    ('id-token', False, KToken('abc', 'Id'), KToken('abc', 'Id')),
    ('add-aexp', False, KToken('3 + 4', 'AExp'), KApply('_+_', [intToken(3), intToken(4)])),
    ('add-int', True, KToken('3 +Int V', 'Int'), KApply('_+Int_', [intToken(3), KVariable('V', sort=INT)])),
    ('k-cell', True, KToken('<k> . </k>', 'KCell'), KApply('<k>', KSequence())),
    (
        'imp-config',
        True,
        KToken(
            """
            <generatedTop>
                <T>
                    <k> int #token("x", "Id") ; #token("x", "Id") = 0 ; </k>
                    <state> .Map </state>
                </T>
                <generatedCounter>
                    0
                </generatedCounter>
            </generatedTop>
            """,
            'GeneratedTopCell',
        ),
        KApply(
            '<generatedTop>',
            KApply(
                '<T>',
                KApply(
                    '<k>',
                    KApply(
                        'int_;_',
                        KApply('_,_', KToken('x', 'Id'), KApply('.List{"_,_"}')),
                        KApply('_=_;', KToken('x', 'Id'), KToken('0', 'Int')),
                    ),
                ),
                KApply('<state>', KApply('.Map')),
            ),
            KApply('<generatedCounter>', KToken('0', 'Int')),
        ),
    ),
)


class TestParseToken(KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @pytest.mark.parametrize(
        'test_id,as_rule,token,expected',
        PARSE_TOKEN_TEST_DATA,
        ids=[test_id for test_id, *_ in PARSE_TOKEN_TEST_DATA],
    )
    def test_parse_token(
        self,
        kprint: KPrint,
        test_id: str,
        as_rule: bool,
        token: KToken,
        expected: KInner,
    ) -> None:
        # When
        actual = kprint.parse_token(token, as_rule=as_rule)

        # Then
        assert remove_attrs(actual) == expected

    # Test that printing a definition is possible without error.
    def test_print_definition(self, kprint: KPrint) -> None:
        kprint.pretty_print(kprint.definition)


EMPTY_CONFIG_TEST_DATA: Final = (
    (
        'generatedTop',
        GENERATED_TOP_CELL,
        (
            '<generatedTop>\n'
            '  <T>\n'
            '    <k>\n'
            '      K_CELL\n'
            '    </k>\n'
            '    <state>\n'
            '      STATE_CELL\n'
            '    </state>\n'
            '  </T>\n'
            '  <generatedCounter>\n'
            '    GENERATEDCOUNTER_CELL\n'
            '  </generatedCounter>\n'
            '</generatedTop>'
        ),
    ),
    (
        'TCell',
        KSort('TCell'),
        '<T>\n  <k>\n    K_CELL\n  </k>\n  <state>\n    STATE_CELL\n  </state>\n</T>',
    ),
    (
        'stateCell',
        KSort('StateCell'),
        '<state>\n  STATE_CELL\n</state>',
    ),
)


INIT_CONFIG_TEST_DATA: Final = (
    (
        'generatedTop-no-map',
        GENERATED_TOP_CELL,
        (
            '<generatedTop>\n'
            '  <T>\n'
            '    <k>\n'
            '      $PGM\n'
            '    </k>\n'
            '    <state>\n'
            '      .Map\n'
            '    </state>\n'
            '  </T>\n'
            '  <generatedCounter>\n'
            '    0\n'
            '  </generatedCounter>\n'
            '</generatedTop>'
        ),
    ),
    (
        'TCell-no-map',
        KSort('TCell'),
        '<T>\n  <k>\n    $PGM\n  </k>\n  <state>\n    .Map\n  </state>\n</T>',
    ),
    (
        'stateCell-no-map',
        KSort('StateCell'),
        '<state>\n  .Map\n</state>',
    ),
)


PRETTY_PRINT_IMP_TEST_DATA: Iterable[tuple[str, KInner, str]] = (
    (
        'imp-config',
        KApply(
            '<T>',
            KApply(
                '<k>',
                KApply(
                    'int_;_',
                    KApply(
                        '_,_',
                        KToken('x', 'Id'),
                        KApply(
                            '_,_',
                            KToken('y', 'Id'),
                            KApply('.List{"_,_"}'),
                        ),
                    ),
                ),
            ),
            KApply('<state>', KApply('.Map')),
        ),
        ('<T>\n  <k>\n    int x , y ;\n  </k>\n  <state>\n    .Map\n  </state>\n</T>'),
    ),
)


class TestImpDefn(KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['_,_'] = assoc_with_unit(' , ', '')
        symbol_table['.List{"_,_"}'] = lambda: ''

    @pytest.mark.parametrize(
        'test_id,kast,expected', PRETTY_PRINT_IMP_TEST_DATA, ids=[test_id for test_id, *_ in PRETTY_PRINT_IMP_TEST_DATA]
    )
    def test_pretty_print(self, kprint: KPrint, test_id: str, kast: KInner, expected: str) -> None:
        actual = kprint.pretty_print(kast)
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,sort,expected', EMPTY_CONFIG_TEST_DATA, ids=[test_id for test_id, *_ in EMPTY_CONFIG_TEST_DATA]
    )
    def test_empty_config(self, kprint: KPrint, test_id: str, sort: KSort, expected: str) -> None:
        # When
        empty_config = kprint.definition.empty_config(sort)
        actual = kprint.pretty_print(empty_config)

        # Then
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,sort,expected', INIT_CONFIG_TEST_DATA, ids=[test_id for test_id, *_ in INIT_CONFIG_TEST_DATA]
    )
    def test_init_config(self, kprint: KPrint, test_id: str, sort: KSort, expected: str) -> None:
        # When
        init_config = kprint.definition.init_config(sort)
        actual = kprint.pretty_print(init_config)

        # Then
        assert actual == expected


PRETTY_PRINT_ALIAS_TEST_DATA: Iterable[tuple[str, KInner, str]] = (
    (
        'simple-int',
        KToken('100', 'Int'),
        'hundred',
    ),
    (
        'ac-bool-pred-simple',
        andBool([leInt(intToken(0), KVariable('X')), ltInt(KVariable('X'), intToken(100))]),
        'rangeHundred ( X )',
    ),
    (
        'ac-bool-pred-reversed',
        andBool([ltInt(KVariable('X'), intToken(100)), leInt(intToken(0), KVariable('X'))]),
        # TODO: Actually want 'rangeHundred ( X )'
        'X <Int hundred andBool 0 <=Int X',
    ),
    (
        'ac-bool-pred-separated',
        andBool(
            [leInt(intToken(0), KVariable('X')), ltInt(intToken(3), intToken(4)), ltInt(KVariable('X'), intToken(100))]
        ),
        # TODO: Actually want 'rangeHundred ( X ) andBool 3 <Int 4'
        '0 <=Int X andBool 3 <Int 4 andBool X <Int hundred',
    ),
)

PRETTY_PRINT_NONTERM_LABEL_TEST_DATA: Iterable[tuple[str, KInner, str]] = (
    (
        'all-labeled',
        KApply(
            'labeled',
            KToken('1', 'Int'),
            KToken('2', 'Int'),
        ),
        ('labeled ( ... label1: 1 , label2: 2 )'),
    ),
    (
        'some-labeled',
        KApply(
            'some-labeled',
            KToken('1', 'Int'),
            KToken('2', 'Int'),
        ),
        ('someLabeled ( 1 , 2 )'),
    ),
    (
        'none-labeled',
        KApply(
            'none-labeled',
            KToken('1', 'Int'),
            KToken('2', 'Int'),
        ),
        ('noneLabeled ( 1 , 2 )'),
    ),
    (
        'no-nonterms',
        KApply('no-nonterms', []),
        ('nonNonTerms ( )'),
    ),
)


class TestUnparsingDefn(KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'unparsing.k'

    @pytest.mark.parametrize(
        'test_id,kast,expected',
        PRETTY_PRINT_ALIAS_TEST_DATA,
        ids=[test_id for test_id, *_ in PRETTY_PRINT_ALIAS_TEST_DATA],
    )
    def test_aliases(self, kprint: KPrint, test_id: str, kast: KInner, expected: str) -> None:
        actual = kprint.pretty_print(kast)
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,kast,expected',
        PRETTY_PRINT_NONTERM_LABEL_TEST_DATA,
        ids=[test_id for test_id, *_ in PRETTY_PRINT_NONTERM_LABEL_TEST_DATA],
    )
    def test_nonterm_labels(self, kprint: KPrint, test_id: str, kast: KInner, expected: str) -> None:
        actual = kprint.pretty_print(kast)
        assert actual == expected


SORT_COLLECTIONS_TEST_DATA: Iterable[tuple[str, KInner, str]] = (
    (
        'single-item',
        set_of([token(1)]),
        'SetItem ( 1 )',
    ),
    (
        'two-item',
        set_of([token(1), token(2)]),
        'SetItem ( 1 ) SetItem ( 2 )',
    ),
    (
        'two-item-reversed',
        set_of([token(2), token(1)]),
        'SetItem ( 1 ) SetItem ( 2 )',
    ),
    (
        'account-cell-map-items',
        KApply(
            '_AccountCellMap_',
            [
                KApply('AccountCellMapItem', [KApply('<id>', [token(2)]), KVariable('V1')]),
                KApply('AccountCellMapItem', [KApply('<id>', [token(1)]), KVariable('V2')]),
            ],
        ),
        'V1 V2',
    ),
    (
        'account-cell-map-items-reversed',
        KApply(
            '_AccountCellMap_',
            [
                KApply('AccountCellMapItem', [KApply('<id>', [token(1)]), KVariable('V2')]),
                KApply('AccountCellMapItem', [KApply('<id>', [token(2)]), KVariable('V1')]),
            ],
        ),
        'V1 V2',
    ),
)


class TestSortCollections(KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'cell-map.k'

    @pytest.mark.parametrize(
        'test_id,kast,expected',
        SORT_COLLECTIONS_TEST_DATA,
        ids=[test_id for test_id, *_ in SORT_COLLECTIONS_TEST_DATA],
    )
    def test_pretty_print(self, kprint: KPrint, test_id: str, kast: KInner, expected: str) -> None:
        actual = kprint.pretty_print(inline_cell_maps(kast), sort_collections=True)
        assert actual == expected
