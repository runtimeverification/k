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
        # When
        config = KApply('<T>', [KApply('<k>', [KApply('int_;_', [KApply('_,_', [KToken('x', 'Id'), KApply('_,_', [KToken('y', 'Id'), KConstant('.List{"_,_"}')])])])]), KApply('<state>', [KConstant('.Map')])])

        # Then
        config_expected = '\n'.join([ '<T>'
                                    , '  <k>'
                                    , '    int x , y ;'
                                    , '  </k>'
                                    , '  <state>'
                                    , '    .Map'
                                    , '  </state>'
                                    , '</T>'
                                    ])
        self.assertEqual(config_expected, self.kprove.prettyPrint(config))

    def test_print_prove_rewrite(self):
        # When
        claim_rewrite = KRewrite( KApply('<T>', [ KApply('<k>', [KApply('_+_', [KVariable('X'), KVariable('Y')])])
                                                , KApply('<state>', [KVariable('STATE')])
                                                ])
                                , KApply('<T>', [ KApply('<k>', [KApply('_+Int_', [KVariable('X'), KVariable('Y')])])
                                                , KApply('<state>', [KVariable('STATE')])
                                                ])
                                )
        minimized_claim_rewrite = pushDownRewrites(claim_rewrite)
        claim = KClaim(minimized_claim_rewrite)

        # Then
        minimized_claim_rewrite_expected = '\n'.join([ '<T>'
                                                     , '  <k>'
                                                     , '    ( X + Y => X +Int Y )'
                                                     , '  </k>'
                                                     , '  <state>'
                                                     , '    STATE'
                                                     , '  </state>'
                                                     , '</T>'
                                                     ])
        minimized_claim_rewrite_actual = self.kprove.prettyPrint(minimized_claim_rewrite)
        self.assertEqual(minimized_claim_rewrite_expected, minimized_claim_rewrite_actual)

        # And Then
        result = self.kprove.proveClaim(claim, 'simple-step')
        self.assertEqual('#Top', result['label'])

    def test_bool_simplify(self):
        # When
        bool_test_1 = KApply('_andBool_', [boolToken(False), boolToken(True)])
        bool_test_2 = KApply('_andBool_', [KApply('_==Int_', [intToken(3), intToken(4)]), boolToken(True)])
        bool_test_1_simplified = simplifyBool(bool_test_1)
        bool_test_2_simplified = simplifyBool(bool_test_2)

        # Then
        self.assertEqual(boolToken(False), bool_test_1_simplified)
        self.assertEqual(KApply('_==Int_', [intToken(3), intToken(4)]), bool_test_2_simplified)


def boolToken(b):
    return KToken('true' if b else 'false', 'Bool')


def intToken(i):
    return KToken(str(i), 'Int')
