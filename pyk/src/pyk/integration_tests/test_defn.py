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
        empty_config_generated_top = self.kprove.definition.empty_config(Sorts.GENERATED_TOP_CELL)
        empty_config_t = self.kprove.definition.empty_config(KSort('TCell'))

        empty_config_generated_top_printed = (
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
        )

        # fmt: off
        empty_config_t_printed = (
            f'<T>\n'
            f'  <k>\n'
            f'    K_CELL\n'
            f'  </k>\n'
            f'  <state>\n'
            f'    STATE_CELL\n'
            f'  </state>\n'
            f'</T>'
        )
        # fmt: on

        self.assertEqual(empty_config_generated_top_printed, self.kprove.pretty_print(empty_config_generated_top))
        self.assertEqual(empty_config_t_printed, self.kprove.pretty_print(empty_config_t))
