from typing import Dict, Final, Tuple
from unittest import TestCase

from ..kast import KApply, KInner, KLabel, KVariable, Subst
from ..kastManip import extract_subst
from ..prelude import Bool, mlAnd, mlEquals, mlEqualsTrue, mlTop, token
from .mock_kprint import MockKPrint
from .utils import a, b, c, f, g, h, x, y, z


class SubstTest(TestCase):

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
                actual = dict((Subst(subst1) * Subst(subst2)).minimize())

                # Then
                self.assertDictEqual(actual, expected)

    def test_union(self):
        # Given
        test_data = (
            ({}, {}, {}),
            ({'x': x}, {}, {'x': x}),
            ({}, {'x': x}, {'x': x}),
            ({'x': x, 'y': y}, {'x': x}, {'x': x, 'y': y}),
            ({'x': x, 'y': y}, {'z': z}, {'x': x, 'y': y, 'z': z}),
            ({'x': x}, {'x': y}, None),
            ({'x': x, 'y': y}, {'x': y}, None),
        )

        for i, [subst1, subst2, expected] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = Subst(subst1).union(Subst(subst2))

                # Then
                if expected is None:
                    self.assertIsNone(actual)
                else:
                    self.assertIsNotNone(actual)
                    self.assertDictEqual(dict(actual), expected)

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

    def test_unapply(self):
        # Given
        test_data = (
            (a, {}, a),
            (a, {'x': a}, x),
            (y, {'x': y}, x),
            (f(a), {'x': f(a)}, x),
            (f(f(a)), {'x': f(a)}, f(x)),
            (f(x), {'x': f(a)}, f(x)),
            (f(x), {'x': f(x)}, x),
        )

        for i, [term, subst, expected] in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = Subst(subst).unapply(term)

                # Then
                self.assertEqual(actual, expected)

    def test_pretty(self):
        self.assertListEqual(
            list(Subst({'X': Bool.true, 'Y': KApply('_andBool_', [Bool.true, Bool.true])}).pretty(MockKPrint())),
            ['X |-> true', 'Y |-> _andBool_ ( true , true )']
        )


class ExtractSubstTest(TestCase):
    _0 = token(0)
    _EQ = KLabel('_==Int_')

    TEST_DATA: Final[Tuple[Tuple[KInner, Dict[str, KInner], KInner], ...]] = (
        (a, {}, a),
        (mlEquals(a, b), {}, mlEquals(a, b)),
        (mlEquals(x, a), {'x': a}, mlTop()),
        (mlEquals(x, _0), {}, mlEquals(x, _0)),
        (mlEquals(x, y), {}, mlEquals(x, y)),
        (mlAnd([mlEquals(a, b), mlEquals(x, a)]), {'x': a}, mlEquals(a, b)),
        (mlEqualsTrue(_EQ(a, b)), {}, mlEqualsTrue(_EQ(a, b))),
        (mlEqualsTrue(_EQ(x, a)), {'x': a}, mlTop()),
    )

    def test(self):
        for i, [term, expected_subst, expected_term] in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                actual_subst, actual_term = extract_subst(term)

                # Then
                self.assertDictEqual(dict(actual_subst), expected_subst)
                self.assertEqual(actual_term, expected_term)


class PropogateSubstTest(TestCase):

    def test(self):
        # Given
        v1 = KVariable('V1')
        x = KVariable('X')
        bar_x = KApply('bar', [x])
        config = KApply('<k>', [bar_x])

        subst_conjunct = mlEquals(v1, bar_x)
        other_conjunct = mlEqualsTrue(KApply('_<=Int_', [v1, KApply('foo', [x, bar_x])]))

        term = mlAnd([config, subst_conjunct, other_conjunct])
        term_wo_subst = mlAnd([config, other_conjunct])

        # When
        subst, _ = extract_subst(term)
        actual = subst.unapply(term_wo_subst)

        # Then
        expected_config = KApply('<k>', [v1])
        expected_conjunct = mlEqualsTrue(KApply('_<=Int_', [v1, KApply('foo', [x, v1])]))
        expected = mlAnd([expected_config, expected_conjunct])

        self.assertEqual(actual, expected)
