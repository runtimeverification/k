from typing import Final, Iterable, List, Tuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KSequence, KSort, KToken, KVariable, Subst
from pyk.kast.manip import get_cell
from pyk.kcfg import KCFGExplore
from pyk.ktool import KPrint
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlTop

from ..utils import KCFGExploreTest

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
        (Subst({'X': intToken(3)}), mlTop()),
    ),
    (
        'variable-subst',
        ('int $n , $s ; $n = X ;', '.Map'),
        ('int $n , $s ; $n = Y ;', '.Map'),
        (Subst({'X': KVariable('Y', sort=KSort('AExp'))}), mlTop()),
    ),
    (
        'trivial',
        ('int $n , $s ; $n = 3 ;', '.Map'),
        ('int $n , $s ; $n = 3 ;', '.Map'),
        (Subst({}), mlTop()),
    ),
)


class TestImpProof(KCFGExploreTest):
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

    @pytest.mark.parametrize(
        'test_id,depth,pre,expected_depth,expected_post,expected_next_states',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kcfg_explore: KCFGExplore,
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
        actual_depth, actual_post_term, actual_next_terms = kcfg_explore.cterm_execute(
            self.config(kcfg_explore.kprint, k, state), depth=depth
        )
        actual_k = kcfg_explore.kprint.pretty_print(get_cell(actual_post_term.kast, 'K_CELL'))
        actual_state = kcfg_explore.kprint.pretty_print(get_cell(actual_post_term.kast, 'STATE_CELL'))

        actual_next_states = [
            (
                kcfg_explore.kprint.pretty_print(get_cell(s.kast, 'K_CELL')),
                kcfg_explore.kprint.pretty_print(get_cell(s.kast, 'STATE_CELL')),
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
        kcfg_explore: KCFGExplore,
        test_id: str,
        antecedent: Tuple[str, str],
        consequent: Tuple[str, str],
        expected: Tuple[Subst, KInner],
    ) -> None:
        # Given
        antecedent_term = self.config(kcfg_explore.kprint, *antecedent)
        consequent_term = self.config(kcfg_explore.kprint, *consequent)

        # When
        actual = kcfg_explore.cterm_implies(antecedent_term, consequent_term)

        # Then
        assert actual == expected
