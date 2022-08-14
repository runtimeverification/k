from ..kast import KApply, KClaim, KRewrite, KSort, KToken, KVariable, assocWithUnit, constLabel
from ..kastManip import push_down_rewrites
from ..ktool import KompileBackend
from ..prelude import Sorts
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
            f'<T>\n'
            f'  <k>\n'
            f'    int x , y ;\n'
            f'  </k>\n'
            f'  <state>\n'
            f'    .Map\n'
            f'  </state>\n'
            f'</T>'
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
            f'<T>\n'
            f'  <k>\n'
            f'    ( X + Y => X +Int Y )\n'
            f'  </k>\n'
            f'  <state>\n'
            f'    STATE\n'
            f'  </state>\n'
            f'</T>'
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
                'generatedTop-no-map',
                Sorts.GENERATED_TOP_CELL,
                (
                    f'<generatedTop>\n'
                    f'  <T>\n'
                    f'    <k>\n'
                    f'      K_CELL\n'
                    f'    </k>\n'
                    f'    <state>\n'
                    f'      STATE_CELL\n'
                    f'    </state>\n'
                    f'  </T>\n'
                    f'  <generatedCounter>\n'
                    f'    GENERATEDCOUNTER_CELL\n'
                    f'  </generatedCounter>\n'
                    f'</generatedTop>'
                ),
            ),
            (
                'TCell-no-map',
                KSort('TCell'),
                (
                    f'<T>\n'
                    f'  <k>\n'
                    f'    K_CELL\n'
                    f'  </k>\n'
                    f'  <state>\n'
                    f'    STATE_CELL\n'
                    f'  </state>\n'
                    f'</T>'
                ),
            ),
            (
                'stateCell-no-map',
                KSort('StateCell'),
                (f'<state>\n' f'  STATE_CELL\n' f'</state>'),
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
                KApply('.Map'),
                (
                    f'<generatedTop>\n'
                    f'  <T>\n'
                    f'    <k>\n'
                    f'      .\n'
                    f'    </k>\n'
                    f'    <state>\n'
                    f'      .Map\n'
                    f'    </state>\n'
                    f'  </T>\n'
                    f'  <generatedCounter>\n'
                    f'    GENERATEDCOUNTER_CELL\n'
                    f'  </generatedCounter>\n'
                    f'</generatedTop>'
                ),
            ),
            (
                'TCell-no-map',
                KSort('TCell'),
                KApply('.Map'),
                (f'<T>\n' f'  <k>\n' f'    .\n' f'  </k>\n' f'  <state>\n' f'    .Map\n' f'  </state>\n' f'</T>'),
            ),
            (
                'stateCell-no-map',
                KSort('StateCell'),
                KApply('.Map'),
                (f'<state>\n' f'  .Map\n' f'</state>'),
            ),
        )

        for name, sort, map, expected in test_data:
            with self.subTest(name):
                init_config = self.kprove.definition.init_config(sort)
                actual = self.kprove.pretty_print(init_config)
                self.assertEqual(actual, expected)
