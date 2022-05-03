from ..kast import KAtt, KClaim, KRule, KToken
from ..ktool import KompileBackend
from .kprove_test import KProveTest


class SimpleProofTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/simple-proofs'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.simple-proof-test'

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_prove_claim_with_lemmas(self):
        # Given
        new_lemma = KRule(KToken('pred1(3) => true', 'Bool'), requires=KToken('pred1(4)', 'Bool'), att=KAtt(atts={'simplification': ''}))
        new_claim = KClaim(KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'), requires=KToken('pred1(4)', 'Bool'))

        # When
        result1 = self.kprove.proveClaim(new_claim, 'claim-without-lemma')
        result2 = self.kprove.proveClaim(new_claim, 'claim-with-lemma', lemmas=[new_lemma])

        # Then
        self.assertNotTop(result1)
        self.assertTop(result2)
