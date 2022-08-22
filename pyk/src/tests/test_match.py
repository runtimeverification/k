from typing import Final, Tuple
from unittest import TestCase

from pyk.kast import KInner

from .utils import a, b, c, f, g, h, x, y, z


class MatchTest(TestCase):
    def test_match_and_subst(self):
        # Given
        test_data: Final[Tuple[Tuple[KInner, KInner], ...]] = (
            (a, a),
            (a, x),
            (f(a), x),
            (f(a), f(a)),
            (f(a), f(x)),
            (f(a, b), f(x, y)),
            (f(a, b, c), f(x, y, z)),
            (f(g(h(a))), f(x)),
            (f(g(h(x))), f(x)),
            (f(a, g(b, h(c))), f(x, y)),
        )

        for i, [term, pattern] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                subst = pattern.match(term)

                # Then
                self.assertIsNotNone(subst)
                self.assertEqual(subst(pattern), term)

    def test_no_match(self):
        # Given
        test_data: Final[Tuple[Tuple[KInner, KInner], ...]] = ((f(x, x), f(x, a)),)

        for i, [term, pattern] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                subst = pattern.match(term)

                # Then
                self.assertIsNone(subst)
