from typing import Final, Iterable, Tuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KAtt, KSequence, KToken, KVariable
from pyk.kast.manip import get_cell
from pyk.kast.outer import KClaim, KRule
from pyk.ktool import KProve
from pyk.prelude.kbool import BOOL
from pyk.prelude.ml import is_top

from .utils import KProveTest

EXECUTE_TEST_DATA: Final = (('simple-branch', 3, ('a', '.Map'), 1, ('b', '.Map'), [('c', '.Map'), ('d', '.Map')]),)


class TestSimpleProof(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'

    def test_prove_claim_with_lemmas(self, kprove: KProve) -> None:
        # Given
        claim = KClaim(
            KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'),
            requires=KToken('pred1(4)', BOOL),
        )
        lemma = KRule(
            KToken('pred1(3) => true', BOOL),
            requires=KToken('pred1(4)', BOOL),
            att=KAtt(atts={'simplification': ''}),
        )

        # When
        result1 = kprove.prove_claim(claim, 'claim-without-lemma')
        result2 = kprove.prove_claim(claim, 'claim-with-lemma', lemmas=[lemma])

        # Then
        assert not is_top(result1)
        assert is_top(result2)

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
        def _config(k: str, state: str) -> CTerm:
            _k_parsed = kprove.parse_token(KToken(k, 'KItem'), as_rule=True)
            _state_parsed = kprove.parse_token(KToken(state, 'Map'), as_rule=True)
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
        k, state = pre
        expected_k, expected_state = expected_post

        # When
        actual_depth, actual_post_term, actual_next_terms = kprove.execute(_config(k, state), depth=depth)
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
