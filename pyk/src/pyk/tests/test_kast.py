from typing import Final, List, Tuple
from unittest import TestCase

from ..kast import (
    BOOL,
    INT,
    STRING,
    KApply,
    KInner,
    KLabel,
    KSequence,
    KVariable,
)

x, y, z = (KVariable(name) for name in ['x', 'y', 'z'])


class KLabelTest(TestCase):
    TEST_DATA: Final[Tuple[List[KInner], ...]] = (
        [],
        [BOOL],
        [BOOL, INT],
        [BOOL, INT, STRING],
    )

    def test_init(self):
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

    def test_init_multiple_values(self):
        # Given
        test_data = self.TEST_DATA[1:]
        expected_message = "KLabel() got multiple values for argument 'params'"

        for i, params in enumerate(test_data):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KLabel('f', *params, params=params)

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)

    def test_init_unkown_keyword(self):
        # Given
        expected_message = "KLabel() got an unexpected keyword argument 'key'"

        for i, params in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KLabel('f', *params, key='value')

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

    def test_init(self):
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

    def test_init_multiple_values(self):
        # Given
        test_data = self.TEST_DATA[1:]
        expected_message = "KApply() got multiple values for argument 'args'"

        for i, args in enumerate(test_data):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KApply('f', *args, args=args)

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)

    def test_init_unkown_keyword(self):
        # Given
        expected_message = "KApply() got an unexpected keyword argument 'key'"

        for i, args in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KApply('f', *args, key='value')

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

    def test_init(self):
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

    def test_init_multiple_values(self):
        # Given
        test_data = self.TEST_DATA[1:]
        expected_message = "KSequence() got multiple values for argument 'items'"

        for i, items in enumerate(test_data):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KSequence(*items, items=items)

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)

    def test_init_unkown_keyword(self):
        # Given
        expected_message = "KSequence() got an unexpected keyword argument 'key'"

        for i, items in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                with self.assertRaises(TypeError) as context:
                    # When
                    KSequence(*items, key='value')

                # Then
                actual_message = context.exception.args[0]
                self.assertEqual(actual_message, expected_message)
