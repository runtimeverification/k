from unittest import TestCase

from pyk.kllvm.ast import CompositeSort, Symbol, Variable


class SymbolTest(TestCase):
    def test_str(self) -> None:
        # Given
        s1 = Symbol("Lbl'Plus")
        s2 = Symbol("Lbl'Plus")
        s2.add_formal_argument(CompositeSort('A'))

        test_data = (
            (s1, "Lbl'Plus{}"),
            (s2, "Lbl'Plus{A{}}"),
        )

        for i, (symbol, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = str(symbol)

                # Then
                self.assertEqual(actual, expected)

    def test_equal(self) -> None:
        a1 = Symbol('A')
        a2 = Symbol('A')
        b1 = Symbol('B')
        self.assertIsNot(a1, a2)
        self.assertEqual(a1, a2)
        self.assertNotEqual(a1, b1)


class VariableTest(TestCase):
    def test_variable(self) -> None:
        # When
        a = Variable('A')

        # Then
        self.assertEqual(a.name, 'A')
        self.assertEqual(str(a), 'A')
