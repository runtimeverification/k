from pyk.cterm import CTerm
from pyk.kast import KApply, KAtt, KClaim, KRule, KToken
from pyk.kastManip import get_cell
from pyk.ktool import KompileBackend
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kbool import BOOL

from .kprove_test import KProveTest


class SimpleProofTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/simple-proofs'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.simple-proof-test'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_prove_claim_with_lemmas(self) -> None:
        # Given
        new_lemma = KRule(
            KToken('pred1(3) => true', BOOL),
            requires=KToken('pred1(4)', BOOL),
            att=KAtt(atts={'simplification': ''}),
        )
        new_claim = KClaim(
            KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'),
            requires=KToken('pred1(4)', BOOL),
        )

        # When
        result1 = self.kprove.prove_claim(new_claim, 'claim-without-lemma')
        result2 = self.kprove.prove_claim(new_claim, 'claim-with-lemma', lemmas=[new_lemma])

        # Then
        self.assertNotTop(result1)
        self.assertTop(result2)


class ImpProofTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.imp'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['.List{"_,_"}_Ids'] = lambda: '.Ids'

    def test_get_basic_block(self) -> None:
        # Given
        new_claim = KClaim(
            KToken(
                '<k> $s = 0 ; while ( 0 <= $n ) { $s = $s + $n ; $n = $n + -1 ; } => . ... </k> <state> $n |-> (N => 0) $s |-> (_ => (N *Int (N +Int 1)) /Int 2) </state>',
                'KCell',
            )
        )

        # When
        post_depth_actual, post_branching_actual, post_state = self.kprove.get_claim_basic_block(
            'imp-basic-block', new_claim
        )
        post_state_pretty_actual = self.kprove.pretty_print(post_state)

        post_depth_expected = 9
        post_branching_expected = True
        post_state_pretty_expected = (
            '<generatedTop>\n'
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
            '</generatedTop>'
        )

        self.assertEqual(post_depth_actual, post_depth_expected)
        self.assertEqual(post_branching_actual, post_branching_expected)
        self.assertEqual(post_state_pretty_actual, post_state_pretty_expected)

    def test_prove_cterm(self) -> None:
        def _config(k: str, state: str) -> CTerm:
            return CTerm(KApply('<T>', (KApply('<k>', (KToken(k, 'K'),)), KApply('<state>', (KToken(state, 'Map'),)))))

        # Given
        pre_state = '.Map'
        post_k = '.'
        post_state = '?_POST_STATE_MAP'

        test_data = (
            ('step-1', ['--depth', '1'], 'int $n , $s ; $n = 3 ;', [('int $s , .Ids ; $n = 3 ;', '$n |-> 0')]),
            ('step-2', ['--depth', '2'], 'int $n , $s ; $n = 3 ;', [('int .Ids ; $n = 3 ;', '$n |-> 0 $s |-> 0')]),
            (
                'branch',
                ['--max-counterexamples', '2', '--depth', '4'],
                'int $n ; if (_B:Bool) { $n = 1; } else { $n = 2; }',
                [('$n = 1 ;', '$n |-> 0'), ('$n = 2 ;', '$n |-> 0')],
            ),
        )

        for name, haskell_args, pre_k, posts_expected_strs in test_data:
            with self.subTest(name):
                # When
                results = self.kprove.prove_cterm(
                    'prove-cterm', _config(pre_k, pre_state), _config(post_k, post_state), haskell_args=haskell_args
                )
                posts_actual = [(get_cell(_p, 'K_CELL'), get_cell(_p, 'STATE_CELL')) for _p in results]
                posts_actual_strs = [
                    (self.kprove.pretty_print(k), self.kprove.pretty_print(s)) for k, s in posts_actual
                ]

                # Then
                self.assertCountEqual(posts_expected_strs, posts_actual_strs)
