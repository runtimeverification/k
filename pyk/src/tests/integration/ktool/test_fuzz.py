from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KSort
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import App, EVar, SortApp
from pyk.ktool.krun import fuzz, kintegers
from pyk.testing import KompiledTest

from ..utils import K_FILES, TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Final

    from hypothesis.strategies import SearchStrategy
    from pytest import FixtureRequest

    from pyk.kore.syntax import Pattern

_LOGGER: Final = logging.getLogger(__name__)

FUZZ_FILES: Path = TEST_DATA_DIR / 'fuzzing'


class TestImpFuzz(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'llvm'

    @pytest.fixture
    def template_config(self, request: FixtureRequest) -> Pattern:
        if request.function.__name__ == 'test_fuzz':
            return KoreParser(Path(FUZZ_FILES / 'imp_comm_config.kore').read_text()).pattern()
        elif request.function.__name__ == 'test_fuzz_fail':
            return KoreParser(Path(FUZZ_FILES / 'imp_lte_config.kore').read_text()).pattern()
        else:
            raise RuntimeError('Unexpected use of fixture template_config')

    @pytest.fixture
    def substs(self) -> dict[EVar, SearchStrategy[Pattern]]:
        var_x = EVar(name='VarX', sort=SortApp('SortInt'))
        var_y = EVar(name='VarY', sort=SortApp('SortInt'))
        return {var_x: kintegers(with_inj=KSort('AExp')), var_y: kintegers(with_inj=KSort('AExp'))}

    @pytest.fixture
    def check_func(self) -> Callable[[Pattern], None]:

        lbl = "Lbl'UndsPipe'-'-GT-Unds'"

        def checkres(p: Pattern) -> Pattern:
            if isinstance(p, App):
                if p.symbol == lbl:
                    left = p.args[0]
                    right = p.args[1]
                    if left.args[0].value.value == 'res':  # type: ignore[attr-defined]
                        val = int(right.args[0].value.value)  # type: ignore[attr-defined]
                        assert val == 0
            return p

        return lambda pattern: pattern.args[0].args[1].args[0].pattern.top_down(checkres)  # type: ignore[attr-defined]

    def test_fuzz(
        self,
        definition_dir: Path,
        template_config: Pattern,
        substs: dict[EVar, SearchStrategy[Pattern]],
        check_func: Callable[[Pattern], None],
    ) -> None:
        fuzz(definition_dir, template_config, substs, check_func)

    def test_fuzz_fail(
        self,
        definition_dir: Path,
        template_config: Pattern,
        substs: dict[EVar, SearchStrategy[Pattern]],
        check_func: Callable[[Pattern], None],
    ) -> None:
        with pytest.raises(AssertionError):
            fuzz(definition_dir, template_config, substs, check_func)
