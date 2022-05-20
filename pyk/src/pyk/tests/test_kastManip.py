from functools import partial
from unittest import TestCase

from ..kast import INT, KApply, KInner, KRewrite, KSequence, KToken, KVariable
from ..kastManip import pushDownRewrites

a, b, c = (KApply(label) for label in ['a', 'b', 'c'])
x, y, z = (KVariable(name) for name in ['x', 'y', 'z'])
f, g, h = (partial(KApply.of, label) for label in ['f', 'g', 'h'])
t = KToken('t', INT)


def int_eq(term1: KInner, term2: KInner) -> KApply:
    return KApply('_==Int_', [term1, term2])


class PushDownRewritesTest(TestCase):

    def test_pushDownRewrites(self):
        # Given
        test_data = (
            (KRewrite(KSequence([f(a), b]), KSequence([f(c), b])), KSequence([f(KRewrite(a, c)), b])),
        )

        for i, (before, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = pushDownRewrites(before)

                # Then
                self.assertEqual(actual, expected)
