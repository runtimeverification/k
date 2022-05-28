import sys
from functools import partial
from unittest import TestCase

from ..kast import TRUE, KApply, KLabel, KRewrite, KSequence, KSort, ktokenDots
from ..kastManip import minimize_term, ml_pred_to_bool, push_down_rewrites

a, b, c = (KApply(label) for label in ['a', 'b', 'c'])
f, g, k = (partial(KApply.of, label) for label in ['f', 'g', '<k>'])


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
            (KApply(KLabel('#Equals', [KSort('Bool'), KSort('GeneratedTopCell')]), [TRUE, f(a)]), f(a)),
        )
        sys.stderr.write(str(test_data))

        for i, (before, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = ml_pred_to_bool(before)

                # Then
                self.assertEqual(actual, expected)
