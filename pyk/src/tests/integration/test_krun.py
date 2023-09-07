from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast.inner import KApply, KSequence, KSort, KToken, Subst
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

    def test_run_pattern(self, krun: KRun) -> None:
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
        actual = krun.run_pattern(pattern)

        # Then
        assert actual == expected
