from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm, cterm_build_rule
from pyk.kast.inner import KApply, KSequence, KToken, KVariable
from pyk.kast.prelude.ml import mlEqualsTrue, mlTop
from pyk.testing import CTermSymbolicTest, KPrintTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final, Union

    from pyk.cterm import CTermSymbolic
    from pyk.ktool.kprint import KPrint

    STATE = Union[tuple[str, str], tuple[str, str, str]]


EXECUTE_TEST_DATA: Iterable[tuple[str, int, STATE, int, STATE, list[STATE]]] = (
    ('branch', 3, ('a', '.Map'), 1, ('b ~> .K', '.Map'), [('c ~> .K', '.Map'), ('d ~> .K', '.Map')]),
    (
        'no-branch',
        1,
        ('foo', '3 |-> M:Int', 'notBool pred1(M:Int)'),
        0,
        ('foo ~> .K', '3 |-> M:Int'),
        [],
    ),
)

SIMPLIFY_TEST_DATA: Final = (('bytes-return', ('mybytes', '.Map'), (r'b"\x00\x90\xa0\n\xa1\xf1a" ~> .K', '.Map')),)

BUILD_RULE_TEST_DATA: Final = (
    (
        'functional-lhs',
        (('mybytes', '.Map'), (r'mybytes ~> .K', '.Map')),
        ('( F_e096a1bd:KItem => mybytes )', '.Map', 'F_e096a1bd:KItem ==K mybytes', 'true'),
    ),
)


class TestSimpleProof(CTermSymbolicTest, KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'simple-proofs.k'
    KOMPILE_ARGS = {'syntax_module': 'SIMPLE-PROOFS'}
    LLVM_ARGS = {'syntax_module': 'SIMPLE-PROOFS'}

    @staticmethod
    def config(kprint: KPrint, k: str, state: str, constraint: str | None = None) -> CTerm:
        _k_parsed = kprint.parse_token(KToken(k, 'K'), as_rule=True)
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
        cterm_symbolic: CTermSymbolic,
        kprint: KPrint,
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
        exec_res = cterm_symbolic.execute(self.config(kprint, *pre), depth=depth)
        actual_k = kprint.pretty_print(exec_res.state.cell('K_CELL'))
        actual_state = kprint.pretty_print(exec_res.state.cell('STATE_CELL'))
        actual_depth = exec_res.depth
        actual_next_states = [
            (
                kprint.pretty_print(s.cell('K_CELL')),
                kprint.pretty_print(s.cell('STATE_CELL')),
            )
            for s, _ in exec_res.next_states
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
        cterm_symbolic: CTermSymbolic,
        kprint: KPrint,
        test_id: str,
        pre: tuple[str, str],
        expected_post: tuple[str, str],
    ) -> None:
        # Given
        k, state = pre
        expected_k, expected_state, *_ = expected_post

        # When
        actual_post, _logs = cterm_symbolic.simplify(self.config(kprint, *pre))
        actual_k = kprint.pretty_print(actual_post.cell('K_CELL'))
        actual_state = kprint.pretty_print(actual_post.cell('STATE_CELL'))

        # Then
        assert actual_k == expected_k
        assert actual_state == expected_state

    @pytest.mark.parametrize(
        'test_id,pre,expected_post',
        BUILD_RULE_TEST_DATA,
        ids=[test_id for test_id, *_ in BUILD_RULE_TEST_DATA],
    )
    def test_cterm_build_rule(
        self,
        cterm_symbolic: CTermSymbolic,
        kprint: KPrint,
        test_id: str,
        pre: tuple[tuple[str, str, str | None], tuple[str, str, str | None]],
        expected_post: tuple[str, str, str | None, str | None],
    ) -> None:
        # Given
        lhs, rhs = pre
        expected_k, expected_state, expected_requires, expected_ensures = expected_post

        # When
        config_lhs = self.config(kprint, *lhs)
        config_rhs = self.config(kprint, *rhs)
        rule, _ = cterm_build_rule(test_id, config_lhs, config_rhs, defunc_with=kprint.definition)
        rule_body_cterm = CTerm.from_kast(rule.body)
        rule_k = kprint.pretty_print(rule_body_cterm.cell('K_CELL'))
        rule_state = kprint.pretty_print(rule_body_cterm.cell('STATE_CELL'))
        rule_requires = kprint.pretty_print(rule.requires)
        rule_ensures = kprint.pretty_print(rule.ensures)

        # Then
        assert rule_k == expected_k
        assert rule_state == expected_state
        assert rule_requires == expected_requires
        assert rule_ensures == expected_ensures
