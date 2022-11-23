from tempfile import NamedTemporaryFile
from unittest import TestCase

from pyk.kllvm.ast import CompositePattern, CompositeSort, Pattern, StringPattern, VariablePattern


class PatternTest(TestCase):
    def test_file_load(self) -> None:
        # Given
        test_data = (
            'A{}(B{}(),C{}())',
            '"string pattern"',
            'XYZ : ABC',
        )

        for text in test_data:
            with self.subTest(text):
                with NamedTemporaryFile(mode='w') as f:
                    f.write(text)
                    f.flush()

                    # When
                    actual = Pattern(f.name)

                # Then
                self.assertEqual(str(actual), text)

    def test_composite(self) -> None:
        # Given
        pattern = CompositePattern('F')
        pattern.add_argument(CompositePattern('A'))
        pattern.add_argument(VariablePattern('X', CompositeSort('S')))

        # When
        actual = pattern.substitute({'X': CompositePattern('B')})

        # Then
        self.assertEqual(str(actual), 'F{}(A{}(),B{}())')

    def test_string(self) -> None:
        # Given
        pattern = StringPattern('abc')

        # Then
        self.assertEqual(str(pattern), '"abc"')
        self.assertEqual(pattern.contents, 'abc')

    def test_variable(self) -> None:
        # Given
        pattern = VariablePattern('X', CompositeSort('S'))

        # When
        actual = pattern.substitute({'X': CompositePattern('A')})

        # Then
        self.assertEqual(str(actual), 'A{}()')
