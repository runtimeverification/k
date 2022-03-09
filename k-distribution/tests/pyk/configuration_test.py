from abc import ABC
from unittest import TestCase

from pyk.kast import KAs, KDefinition, KRule, KSort, KSortSynonym, readKastTerm


class ConfigurationTest(TestCase, ABC):
    COMPILED_JSON_PATH = 'definitions/imp-verification/haskell/imp-verification-kompiled'
    MODULE_NAME = 'IMP-VERIFICATION'
    K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
    T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
    GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
    GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
    GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])

    def setUp(self):
        self.definition = readKastTerm(self.COMPILED_JSON_PATH)
        self.assertIsInstance(self.definition, KDefinition)


class StructurallyFrameKCellTest(ConfigurationTest):

    def test(self):
        # Given
        config_expected = substitute(GENERATED_TOP_CELL_1, {'_DotVar0': ktokenDots})

        # When
        config_actual = structurallyFrameKCell(GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, config_expected)


class RemoveGeneratedCounterTest(ConfigurationTest):

    def first_test(self):
        # When
        config_actual = removeGeneratedCells(GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, T_CELL)

    def second_test(self):
        # When
        config_actual = removeGeneratedCells(GENERATED_TOP_CELL_2)

        # Then
        self.assertEqual(config_actual, T_CELL)


class CollapseDotsTest(ConfigurationTest):

    def test(self):
        # Given
        config_before = substitute(T_CELL, {'MAP': ktokenDots})
        config_expected = KApply('<T>', [K_CELL, ktokenDots])

        # When
        config_actual = collapseDots(config_before)

        # Then
        self.assertEqual(config_actual, config_expected)
