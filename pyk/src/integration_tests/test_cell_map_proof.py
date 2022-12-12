from typing import Final, Iterable, NamedTuple, Tuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KSequence, KToken, KVariable, build_assoc
from pyk.kast.manip import get_cell
from pyk.ktool import KProve

from .utils import KProveTest


class State(NamedTuple):
    pgm: str
    active_accounts: str
    accounts: Iterable[Tuple[str, str]]


EXECUTE_TEST_DATA: Final[Iterable[Tuple[str, int, State, int, State, Iterable[State]]]] = (
    (
        'account-nonexistent',
        1,
        State('#accountNonexistent(1)', 'SetItem(1)', [('1', '2')]),
        1,
        State('false', 'SetItem(1)', [('1', '2')]),
        [],
    ),
)


class TestCellMapProof(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/cell-map.k'

    @pytest.mark.parametrize(
        'test_id,depth,pre,expected_depth,expected_post,expected_next_states',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_my_execute(
        self,
        kprove: KProve,
        test_id: str,
        depth: int,
        pre: State,
        expected_depth: int,
        expected_post: State,
        expected_next_states: Iterable[State],
    ) -> None:
        def _parse(kt: KToken) -> KInner:
            return kprove.parse_token(kt, as_rule=True)

        def _print(k: KInner) -> str:
            return kprove.pretty_print(k)

        def _config(k: str, active_accounts: str, accounts: Iterable[Tuple[str, str]]) -> CTerm:
            _k_parsed = _parse(KToken(k, 'KItem'))
            _active_accounts = _parse(KToken(active_accounts, 'Set'))
            _accounts_parsed = (
                KApply(
                    'AccountCellMapItem',
                    [
                        KApply('<id>', [_parse(KToken(act_id, 'Int'))]),
                        KApply(
                            '<account>',
                            [
                                KApply('<id>', [_parse(KToken(act_id, 'Int'))]),
                                KApply('<balance>', [_parse(KToken(act_state, 'Int'))]),
                            ],
                        ),
                    ],
                )
                for act_id, act_state in accounts
            )
            _accounts = build_assoc(KApply('.AccountCellMap'), '_AccountCellMap_', _accounts_parsed)
            return CTerm(
                KApply(
                    '<generatedTop>',
                    [
                        KApply('<k>', [KSequence([_k_parsed])]),
                        KApply('<activeAccounts>', [_active_accounts]),
                        KVariable('GENERATED_COUNTER_CELL'),
                        KApply('<accounts>', [_accounts]),
                    ],
                )
            )

        # Given
        k, aacounts, accounts = pre
        expected_k, _, _ = expected_post

        # When
        actual_depth, actual_post_term, _ = kprove.execute(_config(k, aacounts, accounts), depth=depth)
        actual_k = _print(get_cell(actual_post_term.kast, 'K_CELL'))

        # Then
        assert actual_depth == expected_depth
        assert actual_k == expected_k
