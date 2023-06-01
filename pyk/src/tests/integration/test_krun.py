from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KSort, KToken, Subst
from pyk.kast.manip import flatten_label
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import App
from pyk.prelude.collections import map_item
from pyk.prelude.kint import intToken
from pyk.testing import KRunTest

from .utils import K_FILES

if TYPE_CHECKING:
    from pyk.kast import KInner
    from pyk.kore.syntax import Pattern
    from pyk.ktool.krun import KRun


class TestImpRun(KRunTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'haskell'

    def test_run(self, krun: KRun) -> None:
        # Given
        init_pgm_token = KToken('int n , s ; n = 2 ; s = 0 ; while ( 0 <= n ) { s = s + n ; n = n + -1 ; }', 'Pgm')
        final_cterm = krun.run(init_pgm_token)

        expected_k = KSequence([])
        expected_map_items = [
            map_item(KToken('s', 'Id'), intToken(3)),
            map_item(KToken('n', 'Id'), intToken(-1)),
        ]

        # When
        actual_k = final_cterm.cell('K_CELL')
        actual_map_items = flatten_label('_Map_', final_cterm.cell('STATE_CELL'))

        assert actual_k == expected_k
        assert set(actual_map_items) == set(expected_map_items)

    def test_run_kore_term(self, krun: KRun) -> None:
        def state(k: KInner, state: KInner) -> Pattern:
            kast = krun.definition.empty_config(KSort('GeneratedTopCell'))
            kast = Subst(
                {
                    'K_CELL': k,
                    'STATE_CELL': state,
                    'GENERATEDCOUNTER_CELL': intToken(0),
                }
            )(kast)
            return krun.kast_to_kore(kast, KSort('GeneratedTopCell'))

        # Given
        x = KToken('x', 'Id')
        pattern = state(
            k=KSequence(
                KApply(
                    'int_;_',
                    KApply('_,_', x, KApply('.List{"_,_"}_Ids')),
                    KApply('_=_;', x, intToken(1)),
                ),
            ),
            state=KApply('.Map'),
        )
        expected = state(
            k=KSequence(),
            state=KApply('_|->_', x, intToken(1)),
        )

        # When
        actual = krun.run_kore_term(pattern)

        # Then
        assert actual == expected


class TestConfigRun(KRunTest):
    KOMPILE_MAIN_FILE = K_FILES / 'config.k'

    def test_run_kore_config(self, krun: KRun) -> None:
        # Given
        fst = int_dv(0)
        snd = int_dv(1)
        expected = App(
            "Lbl'-LT-'generatedTop'-GT-'",
            (),
            (
                App(
                    "Lbl'-LT-'T'-GT-'",
                    (),
                    (
                        App("Lbl'-LT-'first'-GT-'", (), (fst,)),
                        App("Lbl'-LT-'second'-GT-'", (), (snd,)),
                    ),
                ),
                App(
                    "Lbl'-LT-'generatedCounter'-GT-'",
                    (),
                    (int_dv(0),),
                ),
            ),
        )

        # When
        actual = krun.run_kore_config({'FST': fst, 'SND': snd}, depth=0)

        # Then
        assert actual == expected


class TestReturnCodeRun(KRunTest):
    KOMPILE_MAIN_FILE = K_FILES / 'return-code.k'

    @staticmethod
    def _input(value: int) -> KToken:
        return KToken(f'foo({value})', 'Foo')

    def test_run_expect_rc(self, krun: KRun) -> None:
        krun.run(self._input(0))
        krun.run(self._input(67), expect_rc=67)
        krun.run(self._input(3), expect_rc=[1, 2, 3, 4])

        with pytest.raises(RuntimeError):
            krun.run(self._input(7))

        with pytest.raises(RuntimeError):
            krun.run(self._input(7), expect_rc=8)

        with pytest.raises(RuntimeError):
            krun.run(self._input(2), expect_rc=[])

        with pytest.raises(RuntimeError):
            krun.run(self._input(2), expect_rc=(1, 4, 5))
