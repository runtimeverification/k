from abc import ABC
from unittest import TestCase

from pyk.kast import (
    KApply,
    KDefinition,
    KRewrite,
    KSequence,
    KVariable,
    ktokenDots,
    readKastTerm,
)
from pyk.kastManip import (
    buildRule,
    collapseDots,
    getCell,
    removeGeneratedCells,
    structurallyFrameKCell,
    substitute,
)


class ConfigurationTest(TestCase, ABC):
    COMPILED_JSON_PATH = 'definitions/imp-verification/haskell/imp-verification-kompiled/compiled.json'
    MODULE_NAME = 'IMP-VERIFICATION'

    K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
    T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
    GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
    GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
    GENERATED_TOP_CELL_2 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])

    def setUp(self):
        self.definition = readKastTerm(self.COMPILED_JSON_PATH)
        self.assertIsInstance(self.definition, KDefinition)


class StructurallyFrameKCellTest(ConfigurationTest):

    def test(self):
        # Given
        config_expected = substitute(self.GENERATED_TOP_CELL_1, {'_DotVar0': ktokenDots})

        # When
        config_actual = structurallyFrameKCell(self.GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, config_expected)


class RemoveGeneratedCounterTest(ConfigurationTest):

    def test_first(self):
        # When
        config_actual = removeGeneratedCells(self.GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, self.T_CELL)

    def test_second(self):
        # When
        config_actual = removeGeneratedCells(self.GENERATED_TOP_CELL_2)

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


class BuildRuleTest(ConfigurationTest):

    def test(self):
        # Given
        config_pre = self.GENERATED_TOP_CELL_1
        config_post = substitute(self.GENERATED_TOP_CELL_1, {'MAP': KVariable('MAP2')})

        state_cell_expected = KRewrite(KVariable('_MAP'), KVariable('?_MAP2'))
        var_map_expected = {'_MAP': KVariable('MAP'), '?_MAP2': KVariable('MAP2')}

        # When
        rule, var_map_actual = buildRule('id1', config_pre, config_post)
        state_cell_actual = getCell(rule.body, 'STATE_CELL')

        # Then
        self.assertEqual(state_cell_actual, state_cell_expected)
        for k in var_map_expected:
            self.assertEqual(var_map_actual[k], var_map_expected[k])
