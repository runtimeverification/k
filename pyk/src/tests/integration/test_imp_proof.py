from typing import Final, Iterable, Tuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KToken, KVariable
from pyk.kast.manip import get_cell
from pyk.ktool import KPrint, KProve
from pyk.ktool.kprint import SymbolTable

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
