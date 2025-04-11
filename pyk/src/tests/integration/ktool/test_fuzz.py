from __future__ import annotations

import logging
from typing import TYPE_CHECKING

import pytest

from pyk.kore.manip import substitute_vars
from pyk.kore.parser import KoreParser
from pyk.kore.prelude import generated_counter, generated_top, inj, int_dv, k, map_pattern, top_cell_initializer
from pyk.kore.syntax import DV, App, EVar, SortApp, String
from pyk.ktool.kfuzz import KFuzz, kintegers
from pyk.ktool.kprint import _kast
from pyk.testing import KompiledTest

from ..utils import K_FILES, TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final, Mapping

    from pyk.kore.syntax import Pattern

_LOGGER: Final = logging.getLogger(__name__)

FUZZ_FILES: Path = TEST_DATA_DIR / 'fuzzing'

VAR_X = EVar(name='VarX', sort=SortApp('SortInt'))
VAR_Y = EVar(name='VarY', sort=SortApp('SortInt'))


def t(k_cell: Pattern, state_cell: Pattern) -> App:
    return App("Lbl'-LT-'T'-GT-'", (), (k_cell, state_cell))


def state(pattern: Pattern) -> App:
    return App("Lbl'-LT-'state'-GT-'", (), (pattern,))


def subst_on_k_cell(template: Pattern, subst_case: Mapping[EVar, Pattern]) -> Pattern:
    """A substitution function that only applies substitutions within the K cell.
    Used to test custom substitution option in fuzzing and optimize fuzzers by
    restricting changes to relevant parts of the configuration.

    Args:
        template: The template configuration containing variables in the K cell.
        subst_case: A mapping from variables to their replacement patterns.
    """
    match template:
        case App(
            "Lbl'-LT-'generatedTop'-GT-'",
            args=(
                App("Lbl'-LT-'T'-GT-'", args=(k_cell, state_cell)),
                generated_counter_cell,
            ),
        ):
            k_cell = substitute_vars(k_cell, subst_case)
            return generated_top((t(k_cell, state_cell), generated_counter_cell))

    raise ValueError(template)


class TestImpFuzz(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'llvm'
    SUBSTS = {VAR_X: kintegers(with_inj='AExp'), VAR_Y: kintegers(with_inj='AExp')}

    @pytest.fixture
    def kfuzz(self, definition_dir: Path) -> KFuzz:
        return KFuzz(definition_dir)

    @pytest.fixture
    def kfuzz_with_subst(self, definition_dir: Path) -> KFuzz:
        return KFuzz(definition_dir, subst_func=subst_on_k_cell)

    @staticmethod
    def check(p: Pattern) -> None:
        def check_inner(p: Pattern) -> Pattern:
            match p:
                case App("Lbl'UndsPipe'-'-GT-Unds'", args=(key, val)):
                    match key, val:
                        case (
                            App('inj', args=(DV(value=String('res')),)),
                            App('inj', args=(DV(value=String(resval)),)),
                        ):
                            assert resval == '0'

            return p

        p.top_down(check_inner)

    @staticmethod
    def setup_program(definition_dir: Path, text: str) -> Pattern:
        kore_text = _kast(definition_dir=definition_dir, input='program', output='kore', expression=text).stdout

        program_pattern = KoreParser(kore_text).pattern()

        def replace_var_ids(p: Pattern) -> Pattern:
            match p:
                case App('inj', _, (DV(_, String('varx')),)):
                    return VAR_X
                case App('inj', _, (DV(_, String('vary')),)):
                    return VAR_Y
            return p

        program_pattern = program_pattern.top_down(replace_var_ids)
        init_pattern = top_cell_initializer(
            {
                '$PGM': inj(SortApp('SortPgm'), SortApp('SortKItem'), program_pattern),
            }
        )

        return init_pattern

    @staticmethod
    def setup_program_with_config(definition_dir: Path, text: str) -> Pattern:

        kore_text = _kast(definition_dir=definition_dir, input='program', output='kore', expression=text).stdout

        program_pattern = KoreParser(kore_text).pattern()

        def replace_var_ids(p: Pattern) -> Pattern:
            match p:
                case App('inj', _, (DV(_, String('varx')),)):
                    return VAR_X
                case App('inj', _, (DV(_, String('vary')),)):
                    return VAR_Y
            return p

        program_pattern = program_pattern.top_down(replace_var_ids)

        return generated_top((t(k(program_pattern), state(map_pattern())), generated_counter(int_dv(0))))

    def test_fuzz(
        self,
        definition_dir: Path,
        kfuzz: KFuzz,
    ) -> None:
        # Given
        program_text = """
            // Checks the commutativity of addition
            int x, y, a, b, res;
            x = varx;
            y = vary;
            a = x + y;
            b = y + x;
            if ((a <= b) && (b <= a)) { // a == b
                res = 0;
            } else {
                res = 1;
            }
            """

        init_pattern = self.setup_program(definition_dir, program_text)

        # Then
        kfuzz.fuzz_with_check(init_pattern, self.SUBSTS, self.check)

    def test_fuzz_fail(
        self,
        definition_dir: Path,
        kfuzz: KFuzz,
    ) -> None:
        # Given
        program_text = """
            // Checks that x <= y
            int x, y, res;
            x = varx;
            y = vary;
            if (x <= y) {
                res = 0;
            } else {
                res = 1;
            }
            """

        init_pattern = self.setup_program(definition_dir, program_text)

        # Then
        with pytest.raises(AssertionError):
            kfuzz.fuzz_with_check(init_pattern, self.SUBSTS, self.check)

    def test_fuzz_with_subst(
        self,
        definition_dir: Path,
        kfuzz_with_subst: KFuzz,
    ) -> None:
        # Given
        program_text = """
            // Checks the commutativity of addition
            int x, y, a, b, res;
            x = varx;
            y = vary;
            a = x + y;
            b = y + x;
            if ((a <= b) && (b <= a)) { // a == b
                res = 0;
            } else {
                res = 1;
            }
            """

        init_pattern = self.setup_program_with_config(definition_dir, program_text)

        # Then
        kfuzz_with_subst.fuzz_with_check(init_pattern, self.SUBSTS, self.check)
