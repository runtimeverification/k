from functools import partial
from unittest import TestCase

from ..kast import KApply, KRewrite, KSequence, ktokenDots
from ..kastManip import minimizeTerm, push_down_rewrites

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

    def test_minimizeTerm(self):
        # Given
        test_data = (
            (f(k(a)), ['<k>'], f(ktokenDots)),
            (f(k(a)), [], f(k(a))),
        )

        for i, (before, abstract_labels, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = minimizeTerm(before, abstractLabels=abstract_labels)

                # Then
                self.assertEqual(actual, expected)
