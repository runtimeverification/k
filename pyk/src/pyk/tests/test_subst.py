from functools import partial
from unittest import TestCase

from ..kast import KApply, KVariable
from ..subst import Subst

a, b, c = (KApply(label) for label in ['a', 'b', 'c'])
x, y, z = (KVariable(name) for name in ['x', 'y', 'z'])
f, g, h = (partial(KApply.of, label) for label in ['f', 'g', 'h'])


class SubstTest(TestCase):

    def test_eq(self):
        # Given
        test_data = (
            ({}, {}),
            ({'x': x}, {}),
            ({}, {'x': x}),
            ({'x': a}, {'x': a}),
        )

        for i, [subst1, subst2] in enumerate(test_data):
            with self.subTest(i=i):
                # Then
                self.assertEqual(Subst(subst1), Subst(subst2))

    def test_neq(self):
        # Given
        test_data = (
            ({'x': a}, {}),
            ({}, {'x': a}),
            ({'x': a}, {'x': b}),
            ({'x': y}, {'x': z}),
        )

        for i, [subst1, subst2] in enumerate(test_data):
            with self.subTest(i=i):
                # Then
                self.assertNotEqual(Subst(subst1), Subst(subst2))

    def test_compose(self):
        # Given
        test_data = (
            ({}, {}, {}),
            ({'x': x}, {}, {}),
            ({}, {'x': x}, {}),
            ({'x': y}, {}, {'x': y}),
            ({}, {'x': y}, {'x': y}),
            ({'y': x}, {'x': y}, {'y': x}),
            ({'x': z}, {'x': y}, {'x': y}),
            ({'y': z}, {'x': y}, {'x': z, 'y': z}),
            ({'x': y}, {'x': f(x)}, {'x': f(y)}),
            ({'x': f(x)}, {'x': f(x)}, {'x': f(f(x))}),
            ({'y': f(z)}, {'x': f(y)}, {'x': f(f(z)), 'y': f(z)}),
        )

        for i, [subst1, subst2, expected] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = dict(Subst(subst1) * Subst(subst2))

                # Then
                self.assertDictEqual(actual, expected)

    def test_apply(self):
        # Given
        test_data = (
            (a, {}, a),
            (x, {}, x),
            (a, {'x': b}, a),
            (x, {'x': a}, a),
            (f(x), {'x': f(x)}, f(f(x))),
            (f(a, g(x, a)), {'x': b}, f(a, g(b, a))),
            (f(g(h(x, y, z))), {'x': a, 'y': b, 'z': c}, f(g(h(a, b, c))))
        )

        for i, [pattern, subst, expected] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = Subst(subst)(pattern)

                # Then
                self.assertEqual(actual, expected)
