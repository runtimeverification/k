from unittest import TestCase

from pyk.kllvm.ast import CompositeSort, SortVariable


class SortTest(TestCase):
    def test_is_concrete(self) -> None:
        # Given
        test_data = (
            (CompositeSort('A'), True),
            (SortVariable('B'), False),
        )

        for i, (sort, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = sort.is_concrete

                # Then
                self.assertEqual(actual, expected)

    def test_name(self) -> None:
        # Given
        names = ('A', 'SortInt', '')

        for name in names:
            with self.subTest(name):
                # When
                sort = CompositeSort(name)

                # Then
                self.assertEqual(sort.name, name)

    def test_str(self) -> None:
        # Given
        test_data = (
            (CompositeSort('A'), 'A{}'),
            (SortVariable('B'), 'B'),
        )

        for i, (sort, expected) in enumerate(test_data):
            with self.subTest(i=i):
                # When
                actual = str(sort)

                # Then
                self.assertEqual(actual, expected)

    def test_add_argument(self) -> None:
        # Given
        f = CompositeSort('F')
        a = CompositeSort('A')
        b = SortVariable('B')

        # When
        f.add_argument(a)
        f.add_argument(b)

        # Then
        self.assertEqual(str(f), 'F{A{},B}')

    def test_substitution_1(self) -> None:
        # Given
        x = SortVariable('X')
        a = CompositeSort('A')
        expected = a

        # When
        actual = a.substitute({x: a})

        # Then
        self.assertEqual(actual, expected)

    def test_substitution_2(self) -> None:
        x = SortVariable('X')
        y = SortVariable('Y')
        a = CompositeSort('A')
        b = CompositeSort('B')
        c = CompositeSort('C')

        original = CompositeSort('F')
        g1 = CompositeSort('G')
        g1.add_argument(x)
        g1.add_argument(x)
        g1.add_argument(b)
        g1.add_argument(y)
        original.add_argument(g1)

        self.assertEqual(str(original), 'F{G{X,X,B{},Y}}')
        self.assertFalse(original.is_concrete)

        expected = CompositeSort('F')
        g2 = CompositeSort('G')
        g2.add_argument(a)
        g2.add_argument(a)
        g2.add_argument(b)
        g2.add_argument(c)
        expected.add_argument(g2)

        self.assertEqual(str(expected), 'F{G{A{},A{},B{},C{}}}')
        self.assertTrue(expected.is_concrete)

        # When
        actual = original.substitute({x: a, y: c})

        # Then
        self.assertEqual(actual, expected)

    def test_equality(self) -> None:
        # Given
        a1 = CompositeSort('A')
        a2 = CompositeSort('A')
        b1 = SortVariable('B')
        b2 = SortVariable('B')

        # Then
        self.assertIsNot(a1, a2)
        self.assertEqual(a1, a2)
        self.assertIsNot(b1, b2)
        self.assertEqual(b1, b2)
        self.assertNotEqual(a1, b1)
        self.assertNotEqual(a2, b2)
