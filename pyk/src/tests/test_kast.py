from typing import Final, List, Tuple
from unittest import TestCase

from pyk.kast import KApply, KDefinition, KFlatModule, KInner, KLabel, KSequence, KSort, build_assoc
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import INT
from pyk.prelude.string import STRING
from pyk.prelude.utils import token

from .utils import f, x, y, z


class KLabelTest(TestCase):
    TEST_DATA: Final[Tuple[List[KSort], ...]] = (
        [],
        [BOOL],
        [BOOL, INT],
        [BOOL, INT, STRING],
    )

    def test_init(self) -> None:
        for i, params in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                terms = (
                    KLabel('f', params),
                    KLabel('f', *params),
                    KLabel('f', params=params),
                    KLabel(name='f', params=params),
                )

                # Then
                for term in terms:
                    self.assertEqual(term.name, 'f')
                    self.assertTupleEqual(term.params, tuple(params))

    def test_init_multiple_values(self) -> None:
        # Given
        test_data = self.TEST_DATA[1:]
        expected_message = "KLabel() got multiple values for argument 'params'"

        for i, params in enumerate(test_data):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KLabel('f', *params, params=params)  # type: ignore

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)

    def test_init_unkown_keyword(self) -> None:
        # Given
        expected_message = "KLabel() got an unexpected keyword argument 'key'"

        for i, params in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KLabel('f', *params, key='value')  # type: ignore

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)


class KApplyTest(TestCase):
    TEST_DATA: Final[Tuple[List[KInner], ...]] = (
        [],
        [x],
        [x, y],
        [x, y, z],
    )

    def test_init(self) -> None:
        for i, args in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                terms = (
                    KApply('f', args),
                    KApply('f', *args),
                    KApply('f', args=args),
                    KApply(label='f', args=args),
                )

                # Then
                for term in terms:
                    self.assertEqual(term.label, KLabel('f'))
                    self.assertTupleEqual(term.args, tuple(args))

    def test_init_multiple_values(self) -> None:
        # Given
        test_data = self.TEST_DATA[1:]
        expected_message = "KApply() got multiple values for argument 'args'"

        for i, args in enumerate(test_data):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KApply('f', *args, args=args)  # type: ignore

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)

    def test_init_unkown_keyword(self) -> None:
        # Given
        expected_message = "KApply() got an unexpected keyword argument 'key'"

        for i, args in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KApply('f', *args, key='value')  # type: ignore

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)


class KSequenceTest(TestCase):
    TEST_DATA: Final[Tuple[List[KInner], ...]] = (
        [],
        [x],
        [x, y],
        [x, y, z],
    )

    def test_init(self) -> None:
        for i, items in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                terms = (
                    KSequence(items),
                    KSequence(*items),
                    KSequence(items=items),
                )

                # Then
                for term in terms:
                    self.assertTupleEqual(term.items, tuple(items))

    def test_init_multiple_values(self) -> None:
        # Given
        test_data = self.TEST_DATA[1:]
        expected_message = "KSequence() got multiple values for argument 'items'"

        for i, items in enumerate(test_data):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KSequence(*items, items=items)  # type: ignore

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)

    def test_init_unkown_keyword(self) -> None:
        # Given
        expected_message = "KSequence() got an unexpected keyword argument 'key'"

        for i, items in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KSequence(*items, key='value')  # type: ignore

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)


class KDefinitionTest(TestCase):
    def test(self) -> None:
        defn = KDefinition('FOO', [KFlatModule('BAR', [], []), KFlatModule('FOO', [], [])])
        self.assertCountEqual(defn.module_names, ['FOO', 'BAR'])


class BuildAssocTest(TestCase):
    _0: Final = token('0')

    TEST_DATA: Final = (
        ((_0,), _0),
        ((x,), x),
        ((x, _0), x),
        ((_0, x), x),
        ((x, y), f(x, y)),
        ((_0, x, y), f(x, y)),
        ((x, _0, y), f(x, y)),
        ((x, y, _0), f(x, y)),
        ((x, y, z), f(x, f(y, z))),
        ((_0, x, y, z), f(x, f(y, z))),
        ((x, _0, y, z), f(x, f(y, z))),
        ((x, y, _0, z), f(x, f(y, z))),
        ((x, y, z, _0), f(x, f(y, z))),
        ((_0, x, _0, y, _0, z, _0), f(x, f(y, z))),
    )

    def test(self) -> None:
        for i, (terms, expected) in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = build_assoc(self._0, f, terms)

                # Then
                self.assertEqual(actual, expected)
