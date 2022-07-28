from ..kast import (
    KApply,
    KClaim,
    KRewrite,
    KToken,
    KVariable,
    assocWithUnit,
    constLabel,
)
from ..kastManip import push_down_rewrites
from ..ktool import KompileBackend
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
