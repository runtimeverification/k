from typing import List, Tuple
from unittest import TestCase

from pyk.kast import KApply, KInner, KLabel, KRewrite, KSequence, KSort, KVariable
from pyk.kastManip import (
    bool_to_ml_pred,
    collapse_dots,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    simplify_bool,
    split_config_from,
    substitute,
)
from pyk.prelude.k import DOTS, GENERATED_TOP_CELL, K
from pyk.prelude.kbool import BOOL, FALSE, TRUE, andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlEqualsTrue, mlTop

from .utils import a, b, c, f, k, x

K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
GENERATED_TOP_CELL_2 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])


class PushDownRewritesTest(TestCase):
    def test_push_down_rewrites(self) -> None:
        # Given
        test_data = ((KRewrite(KSequence([f(a), b]), KSequence([f(c), b])), KSequence([f(KRewrite(a, c)), b])),)

        for i, (before, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = push_down_rewrites(before)

                # Then
                self.assertEqual(actual, expected)


class MinimizeTermTest(TestCase):
    def test_minimize_term(self) -> None:
        # Given
        test_data: Tuple[Tuple[KInner, List[str], KInner], ...] = (
            (f(k(a)), ['<k>'], f(DOTS)),
            (f(k(a)), [], f(k(a))),
        )

        for i, (before, abstract_labels, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = minimize_term(before, abstract_labels=abstract_labels)

                # Then
                self.assertEqual(actual, expected)


class BoolMlPredConversionsTest(TestCase):

    # TODO: We'd like for bool_to_ml_pred and ml_pred_to_bool to be somewhat invertible.

    test_data_ml_pred_to_bool = (
        (
            'equals-true',
            False,
            KApply(KLabel('#Equals', [BOOL, GENERATED_TOP_CELL]), [TRUE, f(a)]),
            f(a),
        ),
        ('top-sort-bool', False, KApply(KLabel('#Top', [BOOL])), TRUE),
        ('top-no-sort', False, KApply('#Top'), TRUE),
        ('top-no-sort', False, mlTop(), TRUE),
        ('equals-variabl', False, KApply(KLabel('#Equals'), [x, f(a)]), KApply('_==K_', [x, f(a)])),
        ('equals-true-no-sort', False, KApply(KLabel('#Equals'), [TRUE, f(a)]), f(a)),
        (
            'equals-token',
            False,
            KApply(KLabel('#Equals', [KSort('Int'), GENERATED_TOP_CELL]), [intToken(3), f(a)]),
            KApply('_==K_', [intToken(3), f(a)]),
        ),
        ('not-top', False, KApply(KLabel('#Not', [GENERATED_TOP_CELL]), [mlTop()]), notBool(TRUE)),
        ('equals-term', True, KApply(KLabel('#Equals'), [f(a), f(x)]), KApply('_==K_', [f(a), f(x)])),
        (
            'simplify-and-true',
            False,
            KApply(KLabel('#And', [GENERATED_TOP_CELL]), [mlEqualsTrue(TRUE), mlEqualsTrue(TRUE)]),
            TRUE,
        ),
        (
            'ceil-set-concat-no-sort',
            True,
            KApply(
                KLabel('#Ceil', [KSort('Set'), GENERATED_TOP_CELL]),
                [KApply(KLabel('_Set_'), [KVariable('_'), KVariable('_')])],
            ),
            KVariable('Ceil_0f9c9997'),
        ),
        (
            'ceil-set-concat-sort',
            True,
            KApply(
                KLabel('#Not', [GENERATED_TOP_CELL]),
                [
                    KApply(
                        KLabel('#Ceil', [KSort('Set'), GENERATED_TOP_CELL]),
                        [KApply(KLabel('_Set_'), [KVariable('_'), KVariable('_')])],
                    )
                ],
            ),
            notBool(KVariable('Ceil_0f9c9997')),
        ),
        (
            'exists-equal-int',
            True,
            KApply(
                KLabel('#Exists', [INT, BOOL]),
                [KVariable('X'), KApply('_==Int_', [KVariable('X'), KVariable('Y')])],
            ),
            KVariable('Exists_6acf2557'),
        ),
    )

    def test_ml_pred_to_bool(self) -> None:
        for name, unsafe, ml_pred, bool_expected in self.test_data_ml_pred_to_bool:
            with self.subTest(name):
                bool_actual = ml_pred_to_bool(ml_pred, unsafe=unsafe)
                self.assertEqual(bool_actual, bool_expected)

    test_data_bool_to_ml_pred = (('equals-true', KApply(KLabel('#Equals', [BOOL, K]), [TRUE, f(a)]), f(a)),)

    def test_bool_to_ml_pred(self) -> None:
        for name, ml_pred_expected, bool_in in self.test_data_bool_to_ml_pred:
            with self.subTest(name):
                ml_pred_actual = bool_to_ml_pred(bool_in)
                self.assertEqual(ml_pred_actual, ml_pred_expected)


class RemoveGeneratedCellsTest(TestCase):
    def test_first(self) -> None:
        # When
        config_actual = remove_generated_cells(GENERATED_TOP_CELL_1)

        # Then
        self.assertEqual(config_actual, T_CELL)

    def test_second(self) -> None:
        # When
        config_actual = remove_generated_cells(GENERATED_TOP_CELL_2)

        # Then
        self.assertEqual(config_actual, T_CELL)


class CollapseDotsTest(TestCase):
    def test(self) -> None:
        # Given
        config_before = substitute(GENERATED_TOP_CELL_1, {'MAP': DOTS, '_GENERATED_COUNTER_PLACEHOLDER': DOTS})
        config_expected = KApply('<generatedTop>', [KApply('<T>', [K_CELL, DOTS]), DOTS])

        # When
        config_actual = collapse_dots(config_before)

        # Then
        self.assertEqual(config_actual, config_expected)


class SimplifyBoolTest(TestCase):
    def test_simplify_bool(self) -> None:
        # Given
        bool_tests = (
            ('trivial-false', andBool([FALSE, TRUE]), FALSE),
            (
                'and-true',
                andBool([KApply('_==Int_', [intToken(3), intToken(4)]), TRUE]),
                KApply('_==Int_', [intToken(3), intToken(4)]),
            ),
            ('not-false', notBool(FALSE), TRUE),
        )

        for test_name, bool_in, bool_out in bool_tests:
            with self.subTest(test_name):
                # When
                bool_out_actual = simplify_bool(bool_in)

                # Then
                self.assertEqual(bool_out_actual, bool_out)


class SplitConfigTest(TestCase):
    def test_split_config_from(self) -> None:
        k_cell = KSequence([KApply('foo'), KApply('bar')])
        term = KApply('<k>', [k_cell])
        config, subst = split_config_from(term)
        self.assertEqual(config, KApply('<k>', [KVariable('K_CELL')]))
        self.assertEqual(subst, {'K_CELL': k_cell})

        map_item_cell = KApply('<mapItem>', [KApply('foo')])
        map_cell = KApply('<mapCell>', [KApply('map_join', [map_item_cell, map_item_cell])])
        config, subst = split_config_from(map_cell)
        self.assertEqual(config, KApply('<mapCell>', [KVariable('MAPCELL_CELL')]))
        self.assertEqual(subst, {'MAPCELL_CELL': KApply('map_join', [map_item_cell, map_item_cell])})
