from typing import Final, Mapping, Tuple
from unittest import TestCase

from pyk.kast import KInner
from pyk.kastManip import count_vars

from .utils import a, b, c, f, g, h, x, y, z


class CountVarTest(TestCase):
    TEST_DATA: Final[Tuple[Tuple[KInner, Mapping[str, int]], ...]] = (
        (a, {}),
        (x, {'x': 1}),
        (f(a), {}),
        (f(a, b, c), {}),
        (f(x), {'x': 1}),
        (f(f(f(x))), {'x': 1}),
        (f(x, a), {'x': 1}),
        (f(x, x), {'x': 2}),
        (f(x, y), {'x': 1, 'y': 1}),
        (f(x, y, z), {'x': 1, 'y': 1, 'z': 1}),
        (f(x, g(y), h(z)), {'x': 1, 'y': 1, 'z': 1}),
        (f(x, a, g(y, b), h(z, c)), {'x': 1, 'y': 1, 'z': 1}),
        (f(x, g(x, y), h(x, z)), {'x': 3, 'y': 1, 'z': 1}),
        (f(x, g(x, h(x, y, z))), {'x': 3, 'y': 1, 'z': 1}),
    )

    def test(self):
        # Given
        for i, [term, expected] in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = count_vars(term)

                # Then
                self.assertDictEqual(actual, expected)
