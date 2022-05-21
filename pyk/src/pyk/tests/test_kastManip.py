from functools import partial
from unittest import TestCase

from ..kast import KApply, KRewrite, KSequence
from ..kastManip import push_down_rewrites

a, b, c = (KApply(label) for label in ['a', 'b', 'c'])
f, g, h = (partial(KApply.of, label) for label in ['f', 'g', 'h'])


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
