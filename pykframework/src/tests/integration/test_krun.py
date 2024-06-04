from __future__ import annotations

from string import Template
from typing import TYPE_CHECKING

import pytest

import pykframework.kore.match as km
from pykframework.kast.inner import KApply, KSequence, KSort, KToken, Subst
from pykframework.kore.parser import KoreParser
from pykframework.kore.prelude import inj, top_cell_initializer
from pykframework.kore.syntax import SortApp
from pykframework.ktool.kprint import _kast
from pykframework.ktool.krun import llvm_interpret
from pykframework.prelude.kint import intToken
from pykframework.testing import KRunTest
from pykframework.utils import chain

from .utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pykframework.kast import KInner
    from pykframework.kore.syntax import Pattern
    from pykframework.ktool.krun import KRun
    from pykframework.testing import Kompiler


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
                    KApply('_,_', x, KApply('.List{"_,_"}')),
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


@pytest.fixture
def imp_definition(kompile: Kompiler) -> Path:
    return kompile(main_file=K_FILES / 'imp.k')


INTERPRET_TEST_DATA: Final = (
    (0, 0, 0),
    (2, 3, 1),
    (12, 8, 4),
    (4, 8, 4),
    (-8, 6, 2),
    (8, -6, 8),
)


@pytest.mark.parametrize('a,b,expected', INTERPRET_TEST_DATA)
def test_llvm_interpret(imp_definition: Path, a: int, b: int, expected: int) -> None:
    """Run the intepreter on Euclid's algorithm."""

    # Given
    program_text = Template(
        """
        int a, b, c, res;
        a = $a;
        b = $b;
        while (0 < b) {
            c = a % b;
            a = b;
            b = c;
        }
        res = a;
        """
    ).substitute(a=a, b=b)
    kore_text = _kast(definition_dir=imp_definition, input='program', output='kore', expression=program_text).stdout

    program_pattern = KoreParser(kore_text).pattern()
    init_pattern = top_cell_initializer(
        {
            '$PGM': inj(SortApp('SortPgm'), SortApp('SortKItem'), program_pattern),
        }
    )

    # When
    final_pattern = llvm_interpret(imp_definition, init_pattern, depth=1000)
    extract_state = (
        chain
        >> km.app("Lbl'-LT-'generatedTop'-GT-'")
        >> km.arg("Lbl'-LT-'T'-GT-'")
        >> km.arg("Lbl'-LT-'state'-GT-'")
        >> km.arg(0)
        >> km.kore_map_of(
            key=chain >> km.inj >> km.kore_id,
            value=chain >> km.inj >> km.kore_int,
        )
    )
    state = dict(extract_state(final_pattern))
    actual = state['res']

    # Then
    assert actual == expected
