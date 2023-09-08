from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.prelude.ml import mlTop
from pyk.testing import KCFGExploreTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable

    from pyk.kcfg import KCFGExplore


EXECUTE_TEST_DATA: Iterable[tuple[str]] = (('branch',),)


class TestMultipleDefinitionsProof(KCFGExploreTest):
    KOMPILE_MAIN_FILE = K_FILES / 'multiple-definitions.k'

    @staticmethod
    def config() -> CTerm:
        return CTerm(
            KApply(
                '<generatedTop>',
                KApply('<k>', KSequence(KApply('a', [KVariable('X')]))),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
            (mlTop(),),
        )

    @pytest.mark.parametrize(
        'test_id',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kcfg_explore: KCFGExplore,
        test_id: str,
    ) -> None:
        _, split_depth, split_post_term, split_next_terms, _logs = kcfg_explore.cterm_execute(self.config(), depth=1)

        split_k = kcfg_explore.kprint.pretty_print(split_post_term.cell('K_CELL'))
        split_next_k = [kcfg_explore.kprint.pretty_print(split_post_term.cell('K_CELL')) for term in split_next_terms]

        assert split_depth == 0
        assert len(split_next_terms) == 2
        assert 'a ( X:KItem )' == split_k
        assert [
            'a ( X:KItem )',
            'a ( X:KItem )',
        ] == split_next_k

        _, step_1_depth, step_1_post_term, step_1_next_terms, _logs = kcfg_explore.cterm_execute(
            split_next_terms[0], depth=1
        )
        step_1_k = kcfg_explore.kprint.pretty_print(step_1_post_term.cell('K_CELL'))
        assert 'c' == step_1_k

        _, step_2_depth, step_2_post_term, step_2_next_terms, _logs = kcfg_explore.cterm_execute(
            split_next_terms[1], depth=1
        )
        step_2_k = kcfg_explore.kprint.pretty_print(step_1_post_term.cell('K_CELL'))
        assert 'c' == step_2_k
