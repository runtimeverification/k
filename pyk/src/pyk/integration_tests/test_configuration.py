from abc import ABC

from ..kast import (
    KApply,
    KDefinition,
    KSequence,
    KVariable,
    ktokenDots,
    readKastTerm,
)
from ..kastManip import collapseDots, remove_generated_cells, substitute
from ..ktool import KompileBackend
from .kompiled_test import KompiledTest


class ConfigurationTest(KompiledTest, ABC):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp'
    KOMPILE_EMIT_JSON = True

    COMPILED_JSON_PATH = 'definitions/imp/compiled.json'
    MODULE_NAME = 'IMP-VERIFICATION'

    K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
    T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
    GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
    GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
    GENERATED_TOP_CELL_2 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])

    def setUp(self):
        super().setUp()
        self.definition = readKastTerm(self.COMPILED_JSON_PATH)
        self.assertIsInstance(self.definition, KDefinition)


class RemoveGeneratedCellsTest(ConfigurationTest):

    def test_first(self):
        # When
        config_actual = remove_generated_cells(self.GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, self.T_CELL)

    def test_second(self):
        # When
        config_actual = remove_generated_cells(self.GENERATED_TOP_CELL_2)

        # Then
        self.assertEqual(config_actual, self.T_CELL)


class CollapseDotsTest(ConfigurationTest):

    def test(self):
        # Given
        config_before = substitute(self.GENERATED_TOP_CELL_1, {'MAP': ktokenDots, '_GENERATED_COUNTER_PLACEHOLDER': ktokenDots})
        config_expected = KApply('<generatedTop>', [KApply('<T>', [self.K_CELL, ktokenDots]), ktokenDots])

        # When
        config_actual = collapseDots(config_before)

        # Then
        self.assertEqual(config_actual, config_expected)
