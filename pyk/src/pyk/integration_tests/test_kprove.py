from ..cterm import CTerm
from ..kast import KApply, KAtt, KClaim, KRule, KToken
from ..ktool import KompileBackend
from ..prelude import Sorts, mlAnd, mlEqualsTrue
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
        new_lemma = KRule(KToken('pred1(3) => true', Sorts.BOOL), requires=KToken('pred1(4)', Sorts.BOOL), att=KAtt(atts={'simplification': ''}))
        new_claim = KClaim(KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'), requires=KToken('pred1(4)', Sorts.BOOL))

        # When
        result1 = self.kprove.prove_claim(new_claim, 'claim-without-lemma')
        result2 = self.kprove.prove_claim(new_claim, 'claim-with-lemma', lemmas=[new_lemma])

        # Then
        self.assertNotTop(result1)
        self.assertTop(result2)

    def test_prove_claim_rule_profile(self):
        # Given
        new_lemma = KRule(KToken('pred1(3) => true', Sorts.BOOL), requires=KToken('pred1(4)', Sorts.BOOL), att=KAtt(atts={'simplification': ''}))
        new_claim = KClaim(KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'), requires=KToken('pred1(4)', Sorts.BOOL))
        rule_profile = self.KPROVE_USE_DIR + '/rule-profile'

        # When
        _ = self.kprove.prove_claim(new_claim, 'claim-with-lemma', lemmas=[new_lemma], rule_profile=rule_profile)

        # Then
        with open(rule_profile, 'r') as rp:
            lines = rp.read().split('\n')
            self.assertEqual(len(lines), 4)


class ImpProofTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.imp'

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_get_basic_block(self):
        # Given
        new_claim = KClaim(KToken('<k> $s = 0 ; while ( 0 <= $n ) { $s = $s + $n ; $n = $n + -1 ; } => . ... </k> <state> $n |-> (N => 0) $s |-> (_ => (N *Int (N +Int 1)) /Int 2) </state>', 'KCell'))

        # When
        post_depth_actual, post_branching_actual, post_state = self.kprove.get_claim_basic_block('imp-basic-block', new_claim)
        post_state_pretty_actual = self.kprove.pretty_print(post_state)

        post_depth_expected = 9
        post_branching_expected = True
        post_state_pretty_expected = ('<generatedTop>\n'
                                      '  <T>\n'
                                      '    <k>\n'
                                      '      if ( 0 <=Int N ) { { $s = $s + $n ; $n = $n + -1 ; } while ( 0 <= $n ) { $s = $s + $n ; $n = $n + -1 ; } } else { }\n'
                                      '      ~> _DotVar2\n'
                                      '    </k>\n'
                                      '    <state>\n'
                                      '      $n |-> N $s |-> 0\n'
                                      '    </state>\n'
                                      '  </T>\n'
                                      '  <generatedCounter>\n'
                                      '    _DotVar3\n'
                                      '  </generatedCounter>\n'
                                      '</generatedTop>')

        self.assertEqual(post_depth_actual, post_depth_expected)
        self.assertEqual(post_branching_actual, post_branching_expected)
        self.assertEqual(post_state_pretty_actual, post_state_pretty_expected)

    def test_prove_cterm(self) -> None:

        def _config(k: str, state: str) -> CTerm:
            return CTerm(KApply('<T>', (KApply('<k>', (KToken(k, 'K'),)),
                                        KApply('<state>', (KToken(state, 'Map'),)))))

        init = _config('$n', '$n |-> 1')
        final = _config('1', '$n |-> 1')
        result = self.kprove.prove_cterm('prove-cterm-top', init, final)
        self.assertEqual(len(result), 1)
        self.assertTop(result[0])

        # Failing should return 2 result, but get only one.
        # This might be a kprove bug?
        init = _config('if (B:Bool) { $n = 2;  } else { $n = 3; }', '$n |-> 1')
        final = _config('.K', '$n |-> 1')
        result = self.kprove.prove_cterm('prove-cterm-multiple-results', init, final)
        self.assertEqual(len(result), 2)
