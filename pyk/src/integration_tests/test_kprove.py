from typing import List, Tuple

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KAtt, KSequence, KSort, KToken, KVariable, Subst
from pyk.kast.manip import get_cell
from pyk.kast.outer import KClaim, KRule
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import intToken

from .kprove_test import KProveTest


class SimpleProofTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'

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

    def test_execute(self) -> None:
        def _config(k: str, state: str) -> CTerm:
            _k_parsed = self.kprove.parse_token(KToken(k, 'KItem'), as_rule=True)
            _state_parsed = self.kprove.parse_token(KToken(state, 'Map'), as_rule=True)
            # TODO: Why does kompile put <generatedCounter> before <state>?
            return CTerm(
                KApply(
                    '<generatedTop>',
                    [
                        KApply('<k>', [KSequence([_k_parsed])]),
                        KVariable('GENERATED_COUNTER_CELL'),
                        KApply('<state>', [_state_parsed]),
                    ],
                )
            )

        # Given
        test_data = (('simple-branch', 3, ('a', '.Map'), 1, ('b', '.Map'), [('c', '.Map'), ('d', '.Map')]),)

        for (
            name,
            depth,
            (pre_k, pre_state),
            expected_depth,
            (expected_k, expected_state),
            expected_next_states,
        ) in test_data:
            with self.subTest(name):
                # When
                actual_depth, _actual_state, _actual_next_states = self.kprove.execute(
                    _config(pre_k, pre_state), depth=depth
                )
                actual_k = self.kprove.pretty_print(get_cell(_actual_state.kast, 'K_CELL'))
                actual_state = self.kprove.pretty_print(get_cell(_actual_state.kast, 'STATE_CELL'))

                actual_next_states = [
                    (
                        self.kprove.pretty_print(get_cell(s.kast, 'K_CELL')),
                        self.kprove.pretty_print(get_cell(s.kast, 'STATE_CELL')),
                    )
                    for s in _actual_next_states
                ]

                # Then
                self.assertEqual(actual_k, expected_k)
                self.assertEqual(actual_state, expected_state)
                self.assertEqual(actual_depth, expected_depth)
                self.assertCountEqual(actual_next_states, expected_next_states)


class ImpProofTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'

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
            '      if ( 0 <=Int N:Int ) { { $s = $s + $n ; $n = $n + -1 ; } while ( 0 <= $n ) { $s = $s + $n ; $n = $n + -1 ; } } else { }\n'
            '      ~> _DotVar2:K\n'
            '    </k>\n'
            '    <state>\n'
            '      $n |-> N:Int $s |-> 0\n'
            '    </state>\n'
            '  </T>\n'
            '  <generatedCounter>\n'
            '    _DotVar3:Int\n'
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

    def test_execute(self) -> None:
        def _config(k: str, state: str) -> CTerm:
            _k_parsed = self.kprove.parse_token(KToken(k, 'Pgm'), as_rule=True)
            _state_parsed = self.kprove.parse_token(KToken(state, 'Map'), as_rule=True)
            return CTerm(
                KApply(
                    '<generatedTop>',
                    [
                        KApply(
                            '<T>',
                            (
                                KApply('<k>', [KSequence([_k_parsed])]),
                                KApply('<state>', [_state_parsed]),
                            ),
                        ),
                        KVariable('GENERATED_COUNTER_CELL'),
                    ],
                )
            )

        # Given
        empty_states: List[Tuple[str, str]] = []
        test_data = (
            (
                'step-1',
                1,
                ('int $n , $s ; $n = 3 ;', '.Map'),
                1,
                ('int $s , .Ids ; $n = 3 ;', '$n |-> 0'),
                empty_states,
            ),
            (
                'step-2',
                2,
                ('int $n , $s ; $n = 3 ;', '.Map'),
                2,
                ('int .Ids ; $n = 3 ;', '$s |-> 0 $n |-> 0'),
                empty_states,
            ),
            (
                'branch',
                4,
                ('int $n ; if (_B:Bool) { $n = 1; } else { $n = 2; }', '.Map'),
                2,
                ('if ( _B:Bool ) { $n = 1 ; } else { $n = 2 ; }', '$n |-> 0'),
                [('{ $n = 1 ; }', '$n |-> 0'), ('{ $n = 2 ; }', '$n |-> 0')],
            ),
        )

        for (
            name,
            depth,
            (pre_k, pre_state),
            expected_depth,
            (expected_k, expected_state),
            expected_next_states,
        ) in test_data:
            with self.subTest(name):
                # When
                actual_depth, _actual_state, _actual_next_states = self.kprove.execute(
                    _config(pre_k, pre_state), depth=depth
                )
                actual_k = self.kprove.pretty_print(get_cell(_actual_state.kast, 'K_CELL'))
                actual_state = self.kprove.pretty_print(get_cell(_actual_state.kast, 'STATE_CELL'))

                actual_next_states = [
                    (
                        self.kprove.pretty_print(get_cell(s.kast, 'K_CELL')),
                        self.kprove.pretty_print(get_cell(s.kast, 'STATE_CELL')),
                    )
                    for s in _actual_next_states
                ]

                # Then
                self.assertEqual(actual_k, expected_k)
                self.assertEqual(actual_state, expected_state)
                self.assertEqual(actual_depth, expected_depth)
                self.assertCountEqual(actual_next_states, expected_next_states)

    def test_implies(self) -> None:
        def _config(k: str, state: str) -> CTerm:
            _k_parsed = self.kprove.parse_token(KToken(k, 'Pgm'), as_rule=True)
            _state_parsed = self.kprove.parse_token(KToken(state, 'Map'), as_rule=True)
            return CTerm(
                KApply(
                    '<generatedTop>',
                    [
                        KApply(
                            '<T>',
                            (
                                KApply('<k>', [KSequence([_k_parsed])]),
                                KApply('<state>', [_state_parsed]),
                            ),
                        ),
                        KVariable('GENERATED_COUNTER_CELL'),
                    ],
                )
            )

        # Given
        test_data = (
            (
                'constant-subst',
                ('int $n , $s ; $n = X ;', '.Map'),
                ('int $n , $s ; $n = 3 ;', '.Map'),
                Subst({'X': intToken(3)}),
            ),
            (
                'variable-subst',
                ('int $n , $s ; $n = X ;', '.Map'),
                ('int $n , $s ; $n = Y ;', '.Map'),
                Subst({'X': KVariable('Y', sort=KSort('AExp'))}),
            ),
        )

        for (
            name,
            (antecedent_k, antecedent_map),
            (consequent_k, consequent_map),
            expected_subst,
        ) in test_data:
            with self.subTest(name):
                antecedent = _config(antecedent_k, antecedent_map)
                consequent = _config(consequent_k, consequent_map)
                # When
                actual_subst = self.kprove.implies(antecedent, consequent)

                # Then
                self.assertEqual(actual_subst, expected_subst)
