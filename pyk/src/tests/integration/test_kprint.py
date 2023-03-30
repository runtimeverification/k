from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable
from pyk.kast.manip import remove_attrs
from pyk.ktool.kprint import assoc_with_unit
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.kint import INT, intToken

from .utils import KPrintTest

if TYPE_CHECKING:
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
                        KApply('_,_', KToken('x', 'Id'), KApply('.List{"_,_"}_Ids')),
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
    KOMPILE_MAIN_FILE = 'k-files/imp.k'

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


class TestDefn(KPrintTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['_,_'] = assoc_with_unit(' , ', '')
        symbol_table['.List{"_,_"}'] = lambda: ''

    def test_pretty_print(self, kprint: KPrint) -> None:
        # Given
        config = KApply(
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
        )

        # fmt: off
        expected = (
            '<T>\n'
            '  <k>\n'
            '    int x , y ;\n'
            '  </k>\n'
            '  <state>\n'
            '    .Map\n'
            '  </state>\n'
            '</T>'
        )
        # fmt: on

        # When
        actual = kprint.pretty_print(config)

        # Then
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
