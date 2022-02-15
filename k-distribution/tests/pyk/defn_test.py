import json
import os
import shutil
from pathlib import Path

from kprove_test import KProveTest
from pyk.kast import (
    KApply,
    KAtt,
    KClaim,
    KConstant,
    KDefinition,
    KRequire,
    KRewrite,
    KRule,
    KToken,
    KVariable,
    assocWithUnit,
    constLabel,
)
from pyk.kastManip import pushDownRewrites, rewriteAnywhereWith, simplifyBool


class DefnTest(KProveTest):
    DEFN_DIR = 'definitions/imp-verification/haskell/imp-verification-kompiled'
    MAIN_FILE_NAME = 'imp-verification.k'
    USE_DIR = f'.defn-test'
    INCLUDE_DIRS = ['k-files']

    @staticmethod
    def _update_symbol_table(symbol_table):
        symbol_table['_,_'] = assocWithUnit(' , ', '')
        symbol_table['.List{"_,_"}'] = constLabel('')

    def test_print_configuration(self):
        # Given
        config = KApply('<T>', [KApply('<k>', [KApply('int_;_', [KApply('_,_', [KToken('x', 'Id'), KApply('_,_', [KToken('y', 'Id'), KConstant('.List{"_,_"}')])])])]), KApply('<state>', [KConstant('.Map')])])
        config_expected = '\n'.join([ '<T>'
                                    , '  <k>'
                                    , '    int x , y ;'
                                    , '  </k>'
                                    , '  <state>'
                                    , '    .Map'
                                    , '  </state>'
                                    , '</T>'
                                    ])

        # When
        config_actual = self.kprove.prettyPrint(config)

        # Then
        self.assertEqual(config_expected, config_actual)

    def test_print_prove_rewrite(self):
        # Given
        claim_rewrite = KRewrite( KApply('<T>', [ KApply('<k>', [KApply('_+_', [KVariable('X'), KVariable('Y')])])
                                                , KApply('<state>', [KVariable('STATE')])
                                                ])
                                , KApply('<T>', [ KApply('<k>', [KApply('_+Int_', [KVariable('X'), KVariable('Y')])])
                                                , KApply('<state>', [KVariable('STATE')])
                                                ])
                                )
        minimized_claim_rewrite_expected = '\n'.join([ '<T>'
                                                     , '  <k>'
                                                     , '    ( X + Y => X +Int Y )'
                                                     , '  </k>'
                                                     , '  <state>'
                                                     , '    STATE'
                                                     , '  </state>'
                                                     , '</T>'
                                                     ])

        # When
        minimized_claim_rewrite = pushDownRewrites(claim_rewrite)
        claim = KClaim(minimized_claim_rewrite)
        minimized_claim_rewrite_actual = self.kprove.prettyPrint(minimized_claim_rewrite)
        result = self.kprove.proveClaim(claim, 'simple-step')

        # Then
        self.assertEqual(minimized_claim_rewrite_expected, minimized_claim_rewrite_actual)
        self.assertEqual('#Top', result['label'])

    def test_bool_simplify(self):
        # Given
        bool_test_1 = KApply('_andBool_', [boolToken(False), boolToken(True)])
        bool_test_2 = KApply('_andBool_', [KApply('_==Int_', [intToken(3), intToken(4)]), boolToken(True)])

        # When
        bool_test_1_simplified = simplifyBool(bool_test_1)
        bool_test_2_simplified = simplifyBool(bool_test_2)

        # Then
        self.assertEqual(boolToken(False), bool_test_1_simplified)
        self.assertEqual(KApply('_==Int_', [intToken(3), intToken(4)]), bool_test_2_simplified)


def boolToken(b):
    return KToken('true' if b else 'false', 'Bool')


def intToken(i):
    return KToken(str(i), 'Int')
