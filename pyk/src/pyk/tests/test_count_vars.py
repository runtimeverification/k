from functools import partial
from typing import Final, Mapping, Tuple
from unittest import TestCase

from ..kast import KApply, KInner, KVariable
from ..kastManip import count_vars

a, b, c = (KApply(label) for label in ['a', 'b', 'c'])
x, y, z = (KVariable(name) for name in ['x', 'y', 'z'])
f, g, h = (partial(KApply, label) for label in ['f', 'g', 'h'])


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
