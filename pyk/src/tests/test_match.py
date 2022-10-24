from typing import Final, Tuple
from unittest import TestCase

from pyk.kast import KInner, KSequence
from pyk.prelude.ml import mlBottom, mlTop

from .utils import a, b, c, f, g, h, x, y, z


class MatchTest(TestCase):
    def test_match_and_subst(self) -> None:
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
            (KSequence([a, x]), KSequence([y])),
            (KSequence([a, b, x]), KSequence([a, y])),
            (KSequence([f(a), b, x]), KSequence([f(z), y])),
            (KSequence([f(a), b, c, x]), KSequence([f(z), y])),
        )

        for i, [term, pattern] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                subst = pattern.match(term)

                # Then
                self.assertIsNotNone(subst)
                assert subst is not None  # https://github.com/python/mypy/issues/4063
                self.assertEqual(subst(pattern), term)

    def test_no_match(self) -> None:
        # Given
        test_data: Final[Tuple[Tuple[KInner, KInner], ...]] = (
            (f(x, x), f(x, a)),
            (mlTop(), mlBottom()),
            (KSequence([a, b, c]), KSequence([x, x])),
        )

        for i, [term, pattern] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                subst = pattern.match(term)

                # Then
                self.assertIsNone(subst)
