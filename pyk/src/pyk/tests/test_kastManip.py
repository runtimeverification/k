from unittest import TestCase

from ..cterm import CTerm
from ..kast import (
    TRUE,
    KApply,
    KLabel,
    KRewrite,
    KSequence,
    KSort,
    KVariable,
    ktokenDots,
)
from ..kastManip import (
    build_rule,
    collapseDots,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    substitute,
)
from ..prelude import Sorts, intToken, mlEqualsTrue, mlTop
from .utils import a, b, c, f, k

x = KVariable('X')
mem = KLabel('<mem>')

T = KLabel('<T>')
K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
GENERATED_TOP_CELL_2 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])


class PushDownRewritesTest(TestCase):

    def test_push_down_rewrites(self):
        # Given
        test_data = (
            (KRewrite(KSequence([f(a), b]), KSequence([f(c), b])), KSequence([f(KRewrite(a, c)), b])),
        )

        for i, (before, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = push_down_rewrites(before)

                # Then
                self.assertEqual(actual, expected)


class BuildRuleTest(TestCase):

    def test_build_rule(self):
        # Given
        test_data = [
            (
                T(k(KVariable('K_CELL')), mem(KVariable('MEM_CELL'))),
                T(k(KVariable('K_CELL')), mem(KApply('_[_<-_]', [KVariable('MEM_CELL'), KVariable('KEY'), KVariable('VALUE')]))),
                ['K_CELL'],
                T(k(KVariable('_K_CELL')), mem(KRewrite(KVariable('MEM_CELL'), KApply('_[_<-_]', [KVariable('MEM_CELL'), KVariable('?_KEY'), KVariable('?_VALUE')]))))
            )
        ]

        for i, (lhs, rhs, keep_vars, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                rule, _ = build_rule(f'test-{i}', CTerm(lhs), CTerm(rhs), keep_vars=keep_vars)
                actual = rule.body

                # Then
                self.assertEqual(actual, expected)


class MinimizeTermTest(TestCase):

    def test_minimize_term(self):
        # Given
        test_data = (
            (f(k(a)), ['<k>'], f(ktokenDots)),
            (f(k(a)), [], f(k(a))),
        )

        for i, (before, abstract_labels, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = minimize_term(before, abstract_labels=abstract_labels)

                # Then
                self.assertEqual(actual, expected)


class MlPredToBoolTest(TestCase):

    def test_ml_pred_to_bool(self):
        # Given
        test_data = (
            (False, KApply(KLabel('#Equals', [Sorts.BOOL, Sorts.GENERATED_TOP_CELL]), [TRUE, f(a)]), f(a)),
            (False, KApply(KLabel('#Top', [Sorts.BOOL])), TRUE),
            (False, KApply('#Top'), TRUE),
            (False, mlTop(), TRUE),
            (False, KApply(KLabel('#Equals'), [x, f(a)]), KApply('_==K_', [x, f(a)])),
            (False, KApply(KLabel('#Equals'), [TRUE, f(a)]), f(a)),
            (False, KApply(KLabel('#Equals', [KSort('Int'), Sorts.GENERATED_TOP_CELL]), [intToken(3), f(a)]), KApply('_==K_', [intToken(3), f(a)])),
            (False, KApply(KLabel('#Not', [Sorts.GENERATED_TOP_CELL]), [mlTop()]), KApply('notBool_', [TRUE])),
            (True, KApply(KLabel('#Equals'), [f(a), f(x)]), KApply('_==K_', [f(a), f(x)])),
            (False, KApply(KLabel('#And', [Sorts.GENERATED_TOP_CELL]), [mlEqualsTrue(TRUE), mlEqualsTrue(TRUE)]), KApply('_andBool_', [TRUE, TRUE])),
            (True, KApply(KLabel('#Ceil', [KSort('Set'), Sorts.GENERATED_TOP_CELL]), [KApply(KLabel('_Set_', [KVariable('_'), KVariable('_')]))]), KVariable('Ceil_37f1b5e5')),
            (True, KApply(KLabel('#Not', [Sorts.GENERATED_TOP_CELL]), [KApply(KLabel('#Ceil', [KSort('Set'), Sorts.GENERATED_TOP_CELL]), [KApply(KLabel('_Set_', [KVariable('_'), KVariable('_')]))])]), KApply('notBool_', [KVariable('Ceil_37f1b5e5')])),
            (True, KApply(KLabel('#Exists', [Sorts.INT, Sorts.BOOL]), [KVariable('X'), KApply('_==Int_', [KVariable('X'), KVariable('Y')])]), KVariable('Exists_6acf2557')),
        )

        for i, (unsafe, before, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = ml_pred_to_bool(before, unsafe=unsafe)

                # Then
                self.assertEqual(actual, expected)


class RemoveGeneratedCellsTest(TestCase):

    def test_first(self):
        # When
        config_actual = remove_generated_cells(GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, T_CELL)

    def test_second(self):
        # When
        config_actual = remove_generated_cells(GENERATED_TOP_CELL_2)

        # Then
        self.assertEqual(config_actual, T_CELL)


class CollapseDotsTest(TestCase):

    def test(self):
        # Given
        config_before = substitute(GENERATED_TOP_CELL_1, {'MAP': ktokenDots, '_GENERATED_COUNTER_PLACEHOLDER': ktokenDots})
        config_expected = KApply('<generatedTop>', [KApply('<T>', [K_CELL, ktokenDots]), ktokenDots])

        # When
        config_actual = collapseDots(config_before)

        # Then
        self.assertEqual(config_actual, config_expected)
