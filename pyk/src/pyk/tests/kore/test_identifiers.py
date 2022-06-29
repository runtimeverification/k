from unittest import TestCase

from pyk.kore.syntax import is_id, is_set_var_id, is_symbol_id


class IdentifierTest(TestCase):
    BASE_TEST_DATA = (
        ('', False),
        ('-', False),
        ("'", False),
        ('0', False),
        ('@', False),
        ('a', True),
        ('A', True),
        ('a0', True),
        ('a-', True),
        ("a'", True),
    )

    ID_TEST_DATA = BASE_TEST_DATA + (('sort', False),)

    SYMBOL_ID_TEST_DATA = ID_TEST_DATA + tuple(('\\' + s, expected) for s, expected in BASE_TEST_DATA) + (('\\sort', True),)

    SET_VARIABLE_ID_TEST_DATA = tuple(('@' + s, expected) for s, expected in BASE_TEST_DATA) + tuple((s, False) for s, _ in ID_TEST_DATA) + (('@sort', True),)

    def test_is_id(self):
        for i, (s, expected) in enumerate(self.ID_TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = is_id(s)

                # Then
                self.assertEqual(actual, expected)

    def test_is_symbol_id(self):
        for i, (s, expected) in enumerate(self.SYMBOL_ID_TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = is_symbol_id(s)

                # Then
                self.assertEqual(actual, expected)

    def test_is_set_variable_id(self):
        for i, (s, expected) in enumerate(self.SET_VARIABLE_ID_TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = is_set_var_id(s)

                # Then
                self.assertEqual(actual, expected)
