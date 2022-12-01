from typing import Final, Iterable, List, Tuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable, Subst
from pyk.kast.manip import get_cell
from pyk.kast.outer import KClaim
from pyk.ktool import KPrint, KProve
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kint import intToken

from .utils import KProveTest

PROVE_CTERM_TEST_DATA: Final = (
    ('step-1', ['--depth', '1'], 'int $n , $s ; $n = 3 ;', [('int $s , .Ids ; $n = 3 ;', '$n |-> 0')]),
    ('step-2', ['--depth', '2'], 'int $n , $s ; $n = 3 ;', [('int .Ids ; $n = 3 ;', '$n |-> 0 $s |-> 0')]),
    (
        'branch',
        ['--max-counterexamples', '2', '--depth', '4'],
        'int $n ; if (_B:Bool) { $n = 1; } else { $n = 2; }',
        [('$n = 1 ;', '$n |-> 0'), ('$n = 2 ;', '$n |-> 0')],
    ),
)

EMPTY_STATES: Final[List[Tuple[str, str]]] = []
EXECUTE_TEST_DATA: Final = (
    (
        'step-1',
        1,
        ('int $n , $s ; $n = 3 ;', '.Map'),
        1,
        ('int $s , .Ids ; $n = 3 ;', '$n |-> 0'),
        EMPTY_STATES,
    ),
    (
        'step-2',
        2,
        ('int $n , $s ; $n = 3 ;', '.Map'),
        2,
        ('int .Ids ; $n = 3 ;', '$s |-> 0 $n |-> 0'),
        EMPTY_STATES,
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


IMPLIES_TEST_DATA: Final = (
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
    (
        'trivial',
        ('int $n , $s ; $n = 3 ;', '.Map'),
        ('int $n , $s ; $n = 3 ;', '.Map'),
        Subst({}),
    ),
)


class TestImpProof(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['.List{"_,_"}_Ids'] = lambda: '.Ids'

    @staticmethod
    def config(kprint: KPrint, k: str, state: str) -> CTerm:
        k_parsed = kprint.parse_token(KToken(k, 'Pgm'), as_rule=True)
        state_parsed = kprint.parse_token(KToken(state, 'Map'), as_rule=True)
        return CTerm(
            KApply(
                '<generatedTop>',
                [
                    KApply(
                        '<T>',
                        (
                            KApply('<k>', [KSequence([k_parsed])]),
                            KApply('<state>', [state_parsed]),
                        ),
                    ),
                    KVariable('GENERATED_COUNTER_CELL'),
                ],
            )
        )

    def test_get_basic_block(self, kprove: KProve) -> None:
        # Given
        new_claim = KClaim(
            KToken(
                '<k> $s = 0 ; while ( 0 <= $n ) { $s = $s + $n ; $n = $n + -1 ; } => . ... </k> <state> $n |-> (N => 0) $s |-> (_ => (N *Int (N +Int 1)) /Int 2) </state>',
                'KCell',
            )
        )

        # When
        post_depth_actual, post_branching_actual, post_state = kprove.get_claim_basic_block(
            'imp-basic-block', new_claim
        )
        post_state_pretty_actual = kprove.pretty_print(post_state)

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

        assert post_depth_actual == post_depth_expected
        assert post_branching_actual == post_branching_expected
        assert post_state_pretty_actual == post_state_pretty_expected

    @pytest.mark.parametrize(
        'test_id,haskell_args,k,expected_next_states',
        PROVE_CTERM_TEST_DATA,
        ids=[test_id for test_id, *_ in PROVE_CTERM_TEST_DATA],
    )
    def test_prove_cterm(
        self,
        kprove: KProve,
        test_id: str,
        haskell_args: Iterable[str],
        k: str,
        expected_next_states: Iterable[Tuple[str, str]],
    ) -> None:
        def config(k: str, state: str) -> CTerm:
            return CTerm(KApply('<T>', (KApply('<k>', (KToken(k, 'K'),)), KApply('<state>', (KToken(state, 'Map'),)))))

        # Given
        state = '.Map'
        expected_k = '.'
        expected_state = '?_POST_STATE_MAP'

        # When
        results = kprove.prove_cterm(
            'prove-cterm', config(k, state), config(expected_k, expected_state), haskell_args=haskell_args
        )
        actual_next_terms = [(get_cell(_p, 'K_CELL'), get_cell(_p, 'STATE_CELL')) for _p in results]
        actual_next_states = [(kprove.pretty_print(k), kprove.pretty_print(s)) for k, s in actual_next_terms]

        # Then
        assert set(actual_next_states) == set(expected_next_states)

    @pytest.mark.parametrize(
        'test_id,depth,pre,expected_depth,expected_post,expected_next_states',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kprove: KProve,
        test_id: str,
        depth: int,
        pre: Tuple[str, str],
        expected_depth: int,
        expected_post: Tuple[str, str],
        expected_next_states: Iterable[Tuple[str, str]],
    ) -> None:
        # Given
        k, state = pre
        expected_k, expected_state = expected_post

        # When
        actual_depth, actual_post_term, actual_next_terms = kprove.execute(self.config(kprove, k, state), depth=depth)
        actual_k = kprove.pretty_print(get_cell(actual_post_term.kast, 'K_CELL'))
        actual_state = kprove.pretty_print(get_cell(actual_post_term.kast, 'STATE_CELL'))

        actual_next_states = [
            (
                kprove.pretty_print(get_cell(s.kast, 'K_CELL')),
                kprove.pretty_print(get_cell(s.kast, 'STATE_CELL')),
            )
            for s in actual_next_terms
        ]

        # Then
        assert actual_k == expected_k
        assert actual_state == expected_state
        assert actual_depth == expected_depth
        assert set(actual_next_states) == set(expected_next_states)

    @pytest.mark.parametrize(
        'test_id,antecedent,consequent,expected',
        IMPLIES_TEST_DATA,
        ids=[test_id for test_id, *_ in IMPLIES_TEST_DATA],
    )
    def test_implies(
        self,
        kprove: KProve,
        test_id: str,
        antecedent: Tuple[str, str],
        consequent: Tuple[str, str],
        expected: Subst,
    ) -> None:
        # Given
        antecedent_term = self.config(kprove, *antecedent)
        consequent_term = self.config(kprove, *consequent)

        # When
        actual = kprove.implies(antecedent_term, consequent_term)

        # Then
        assert actual == expected
