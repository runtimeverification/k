from typing import Final, Iterable, Tuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KToken, KVariable
from pyk.kast.manip import get_cell
from pyk.kcfg import KCFGExplore
from pyk.ktool import KPrint

from ..utils import KCFGExploreTest

EXECUTE_TEST_DATA: Final = (('simple-branch', 3, ('a', '.Map'), 1, ('b', '.Map'), [('c', '.Map'), ('d', '.Map')]),)

SIMPLIFY_TEST_DATA: Final = (('bytes-return', ('mybytes', '.Map'), (r'b"\x00\x90\xa0\n\xa1\xf1a"', '.Map')),)


class TestSimpleProof(KCFGExploreTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'

    @staticmethod
    def config(kprint: KPrint, k: str, state: str) -> CTerm:
        _k_parsed = kprint.parse_token(KToken(k, 'KItem'), as_rule=True)
        _state_parsed = kprint.parse_token(KToken(state, 'Map'), as_rule=True)
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
        'test_id,pre,expected_post',
        SIMPLIFY_TEST_DATA,
        ids=[test_id for test_id, *_ in SIMPLIFY_TEST_DATA],
    )
    def test_simplify(
        self,
        kcfg_explore: KCFGExplore,
        test_id: str,
        pre: Tuple[str, str],
        expected_post: Tuple[str, str],
    ) -> None:
        # Given
        k, state = pre
        expected_k, expected_state = expected_post

        # When
        actual_post = kcfg_explore.cterm_simplify(self.config(kcfg_explore.kprint, k, state))
        actual_k = kcfg_explore.kprint.pretty_print(get_cell(actual_post, 'K_CELL'))
        actual_state = kcfg_explore.kprint.pretty_print(get_cell(actual_post, 'STATE_CELL'))

        # Then
        assert actual_k == expected_k
        assert actual_state == expected_state
