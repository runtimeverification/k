from ..kast import (
    KApply,
    KClaim,
    KRewrite,
    KSort,
    KToken,
    KVariable,
    assocWithUnit,
    constLabel,
)
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
        # Given
        config = KApply('<T>', [KApply('<k>', [KApply('int_;_', [KApply('_,_', [KToken('x', 'Id'), KApply('_,_', [KToken('y', 'Id'), KApply('.List{"_,_"}')])])])]), KApply('<state>', [KApply('.Map')])])
        config_expected = '\n'.join([ '<T>'              # noqa
                                    , '  <k>'            # noqa
                                    , '    int x , y ;'  # noqa
                                    , '  </k>'           # noqa
                                    , '  <state>'        # noqa
                                    , '    .Map'         # noqa
                                    , '  </state>'       # noqa
                                    , '</T>'             # noqa
                                    ])                   # noqa

        # When
        config_actual = self.kprove.pretty_print(config)

        # Then
        self.assertEqual(config_expected, config_actual)

    def test_print_prove_rewrite(self):
        # Given
        claim_rewrite = KRewrite( KApply('<T>', [ KApply('<k>', [KApply('_+_', [KVariable('X'), KVariable('Y')])])     # noqa
                                                , KApply('<state>', [KVariable('STATE')])                              # noqa
                                                ])                                                                     # noqa
                                , KApply('<T>', [ KApply('<k>', [KApply('_+Int_', [KVariable('X'), KVariable('Y')])])  # noqa
                                                , KApply('<state>', [KVariable('STATE')])                              # noqa
                                                ])                                                                     # noqa
                                )                                                                                      # noqa

        minimized_claim_rewrite_expected = '\n'.join([ '<T>'                        # noqa
                                                     , '  <k>'                      # noqa
                                                     , '    ( X + Y => X +Int Y )'  # noqa
                                                     , '  </k>'                     # noqa
                                                     , '  <state>'                  # noqa
                                                     , '    STATE'                  # noqa
                                                     , '  </state>'                 # noqa
                                                     , '</T>'                       # noqa
                                                     ])                             # noqa

        # When
        minimized_claim_rewrite = push_down_rewrites(claim_rewrite)
        claim = KClaim(minimized_claim_rewrite)
        minimized_claim_rewrite_actual = self.kprove.pretty_print(minimized_claim_rewrite)
        result = self.kprove.prove_claim(claim, 'simple-step')

        # Then
        self.assertEqual(minimized_claim_rewrite_expected, minimized_claim_rewrite_actual)
        self.assertTop(result)

    def test_empty_config(self):
        # Given
        empty_config_generated_top = self.kprove.definition.empty_config(Sorts.GENERATED_TOP_CELL)
        empty_config_t = self.kprove.definition.empty_config(KSort('TCell'))

        empty_config_generated_top_printed = '\n'.join([ '<generatedTop>'               # noqa
                                                       , '  <T>'                        # noqa
                                                       , '    <k>'                      # noqa
                                                       , '      K_CELL'                 # noqa
                                                       , '    </k>'                     # noqa
                                                       , '    <state>'                  # noqa
                                                       , '      STATE_CELL'             # noqa
                                                       , '    </state>'                 # noqa
                                                       , '  </T>'                       # noqa
                                                       , '  <generatedCounter>'         # noqa
                                                       , '    GENERATEDCOUNTER_CELL'    # noqa
                                                       , '  </generatedCounter>'        # noqa
                                                       , '</generatedTop>'              # noqa
                                                       ])                               # noqa

        empty_config_t_printed = '\n'.join([ '<T>'                # noqa
                                           , '  <k>'              # noqa
                                           , '    K_CELL'         # noqa
                                           , '  </k>'             # noqa
                                           , '  <state>'          # noqa
                                           , '    STATE_CELL'     # noqa
                                           , '  </state>'         # noqa
                                           , '</T>'               # noqa
                                           ])                     # noqa

        # Then
        self.assertEqual(empty_config_generated_top_printed, self.kprove.pretty_print(empty_config_generated_top))
        self.assertEqual(empty_config_t_printed, self.kprove.pretty_print(empty_config_t))
