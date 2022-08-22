from pyk.kast import KApply, KClaim, KRewrite, KSort, KToken, KVariable, assocWithUnit, constLabel
from pyk.kastManip import push_down_rewrites
from pyk.ktool import KompileBackend
from pyk.prelude import Sorts

from .kprove_test import KProveTest


class DefnTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp-verification'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.defn-test'

    @staticmethod
    def _update_symbol_table(symbol_table):
        symbol_table['_,_'] = assocWithUnit(' , ', '')
        symbol_table['.List{"_,_"}'] = constLabel('')

    def test_print_configuration(self):

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

    def test_print_prove_rewrite(self):

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

    def test_empty_config(self):
        test_data = (
            (
                'generatedTop',
                Sorts.GENERATED_TOP_CELL,
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

    def test_init_config(self):
        test_data = (
            (
                'generatedTop-no-map',
                Sorts.GENERATED_TOP_CELL,
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
