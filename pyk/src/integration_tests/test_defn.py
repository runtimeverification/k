from pyk.kast.inner import KApply, KRewrite, KSort, KToken, KVariable
from pyk.kast.manip import push_down_rewrites
from pyk.kast.outer import KClaim
from pyk.ktool.kprint import SymbolTable, assoc_with_unit
from pyk.prelude.k import GENERATED_TOP_CELL

from .kprove_test import KProveTest


class DefnTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['_,_'] = assoc_with_unit(' , ', '')
        symbol_table['.List{"_,_"}'] = lambda: ''

    def test_print_configuration(self) -> None:

        # fmt: off
        config = KApply('<T>', [KApply('<k>', [KApply('int_;_', [KApply('_,_', [KToken('x', 'Id'), KApply('_,_', [KToken('y', 'Id'), KApply('.List{"_,_"}')])])])]), KApply('<state>', [KApply('.Map')])])

        config_expected = (
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

        config_actual = self.kprove.pretty_print(config)

        self.assertEqual(config_expected, config_actual)

    def test_print_prove_rewrite(self) -> None:

        # fmt: off
        claim_rewrite = KRewrite( KApply('<T>', [ KApply('<k>', [KApply('_+_', [KVariable('X'), KVariable('Y')])])
                                                , KApply('<state>', [KVariable('STATE')])
                                                ])
                                , KApply('<T>', [ KApply('<k>', [KApply('_+Int_', [KVariable('X'), KVariable('Y')])])
                                                , KApply('<state>', [KVariable('STATE')])
                                                ])
                                )
        # fmt: on

        minimized_claim_rewrite_expected = (
            '<T>\n  <k>\n    ( X + Y => X +Int Y )\n  </k>\n  <state>\n    STATE\n  </state>\n</T>'
        )

        minimized_claim_rewrite = push_down_rewrites(claim_rewrite)
        claim = KClaim(minimized_claim_rewrite)
        minimized_claim_rewrite_actual = self.kprove.pretty_print(minimized_claim_rewrite)
        result = self.kprove.prove_claim(claim, 'simple-step')

        self.assertEqual(minimized_claim_rewrite_expected, minimized_claim_rewrite_actual)
        self.assertTop(result)

    def test_empty_config(self) -> None:
        test_data = (
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

        for name, sort, expected in test_data:
            with self.subTest(name):
                empty_config = self.kprove.definition.empty_config(sort)
                actual = self.kprove.pretty_print(empty_config)
                self.assertEqual(actual, expected)

    def test_init_config(self) -> None:
        test_data = (
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

        for name, sort, expected in test_data:
            with self.subTest(name):
                init_config = self.kprove.definition.init_config(sort)
                actual = self.kprove.pretty_print(init_config)
                self.assertEqual(actual, expected)
