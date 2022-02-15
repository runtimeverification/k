import json
from pathlib import Path

from kprove_test import KProveTest
from pyk.kast import KApply, KAtt, KClaim, KRule, KToken, KVariable
from pyk.kastManip import rewriteAnywhereWith


class SimpleProofTest(KProveTest):
    DEFN_DIR = 'definitions/simple-proofs/haskell/simple-proofs-kompiled'
    MAIN_FILE_NAME = 'simple-proofs.k'
    USE_DIR = '.simple-proof-test'
    INCLUDE_DIRS = ['k-files']

    def setUp(self):
        super().setUp()

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_prove_claim_with_lemmas(self):
        # When
        new_lemma = KRule(KToken('pred1(3) => true', 'Bool'), requires=KToken('pred1(4)', 'Bool'), att=KAtt(atts={'simplification': ''}))
        new_claim = KClaim(KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'), requires=KToken('pred1(4)', 'Bool'))
        result1 = self.kprove.proveClaim(new_claim, 'claim-without-lemma')
        result2 = self.kprove.proveClaim(new_claim, 'claim-with-lemma', lemmas = [new_lemma])

        # Then
        self.assertNotEqual(result1['label'], '#Top')
        self.assertEqual(result2['label'], '#Top')


def extract_claims(module):
    return [claim for claim in module['localSentences'] if claim['node'] == 'KClaim']


def eliminate_generated_top(term):
    rule = KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG')
    return rewriteAnywhereWith(rule, term)
