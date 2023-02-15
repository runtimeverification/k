from typing import Final

import pytest

from pyk.kast.inner import KApply, KRewrite, KSort, KToken, KVariable
from pyk.kast.manip import push_down_rewrites
from pyk.kast.outer import KClaim
from pyk.ktool.kprint import KPrint, SymbolTable, assoc_with_unit
from pyk.ktool.kprove import KProve
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.ml import is_top

from .utils import KPrintTest, KProveTest

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
        # fmt: off
        config = KApply('<T>', [KApply('<k>', [KApply('int_;_', [KApply('_,_', [KToken('x', 'Id'), KApply('_,_', [KToken('y', 'Id'), KApply('.List{"_,_"}')])])])]), KApply('<state>', [KApply('.Map')])])
    
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


class TestPrintProveRewrite(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'

    def test_print_prove_rewrite(self, kprove: KProve) -> None:
        # Given
        claim_rewrite = KRewrite(
            KApply(
                '<T>',
                [
                    KApply('<k>', [KApply('_+_', [KVariable('X'), KVariable('Y')])]),
                    KApply('<state>', [KVariable('STATE')]),
                ],
            ),
            KApply(
                '<T>',
                [
                    KApply('<k>', [KApply('_+Int_', [KVariable('X'), KVariable('Y')])]),
                    KApply('<state>', [KVariable('STATE')]),
                ],
            ),
        )

        expected = '<T>\n  <k>\n    ( X + Y => X +Int Y )\n  </k>\n  <state>\n    STATE\n  </state>\n</T>'

        # When
        minimized_claim_rewrite = push_down_rewrites(claim_rewrite)
        claim = KClaim(minimized_claim_rewrite)
        actual = kprove.pretty_print(minimized_claim_rewrite)
        result = kprove.prove_claim(claim, 'simple-step')

        # Then
        assert actual == expected
        assert is_top(result)
