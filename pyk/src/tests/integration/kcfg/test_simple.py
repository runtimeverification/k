from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KToken, KVariable
from pyk.kast.manip import get_cell
from pyk.prelude.ml import mlEqualsTrue, mlTop
from pyk.testing import KCFGExploreTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final, Union

    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprint import KPrint

    STATE = Union[tuple[str, str], tuple[str, str, str]]


EXECUTE_TEST_DATA: Iterable[tuple[str, int, STATE, int, STATE, list[STATE]]] = (
    ('branch', 3, ('a', '.Map'), 1, ('b', '.Map'), [('c', '.Map'), ('d', '.Map')]),
    (
        'no-branch',
        1,
        ('foo', '3 |-> M:Int', 'notBool pred1(M:Int)'),
        0,
        ('foo', '3 |-> M:Int'),
        [],
    ),
)

SIMPLIFY_TEST_DATA: Final = (('bytes-return', ('mybytes', '.Map'), (r'b"\x00\x90\xa0\n\xa1\xf1a"', '.Map')),)


class TestSimpleProof(KCFGExploreTest):
    KOMPILE_MAIN_FILE = K_FILES / 'simple-proofs.k'

    @staticmethod
    def config(kprint: KPrint, k: str, state: str, constraint: str | None = None) -> CTerm:
        _k_parsed = kprint.parse_token(KToken(k, 'KItem'), as_rule=True)
        _state_parsed = kprint.parse_token(KToken(state, 'Map'), as_rule=True)
        _constraint = (
            mlTop()
            if constraint is None
            else mlEqualsTrue(kprint.parse_token(KToken(constraint, 'Bool'), as_rule=True))
        )
        return CTerm(
            KApply(
                '<generatedTop>',
                KApply('<k>', KSequence(_k_parsed)),
                KApply('<state>', _state_parsed),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
            (_constraint,),
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
        pre: tuple[str, str],
        expected_depth: int,
        expected_post: tuple[str, str],
        expected_next_states: Iterable[tuple[str, str]],
    ) -> None:
        # Given
        expected_k, expected_state, *_ = expected_post

        # When
        exec_res = kcfg_explore.cterm_execute(self.config(kcfg_explore.kprint, *pre), depth=depth)
        actual_k = kcfg_explore.kprint.pretty_print(exec_res.state.cell('K_CELL'))
        actual_state = kcfg_explore.kprint.pretty_print(exec_res.state.cell('STATE_CELL'))
        actual_depth = exec_res.depth
        actual_next_states = [
            (
                kcfg_explore.kprint.pretty_print(s.cell('K_CELL')),
                kcfg_explore.kprint.pretty_print(s.cell('STATE_CELL')),
            )
            for s in exec_res.next_states
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
        pre: tuple[str, str],
        expected_post: tuple[str, str],
    ) -> None:
        # Given
        k, state = pre
        expected_k, expected_state, *_ = expected_post

        # When
        actual_post, _logs = kcfg_explore.cterm_simplify(self.config(kcfg_explore.kprint, *pre))
        actual_k = kcfg_explore.kprint.pretty_print(get_cell(actual_post.kast, 'K_CELL'))
        actual_state = kcfg_explore.kprint.pretty_print(get_cell(actual_post.kast, 'STATE_CELL'))

        # Then
        assert actual_k == expected_k
        assert actual_state == expected_state
