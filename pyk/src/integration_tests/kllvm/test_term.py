from pyk.kllvm.ast import CompositePattern

from .utils import RuntimeTest


class TermTest(RuntimeTest):
    KOMPILE_MAIN_FILE = 'k-files/ctor.k'
    KOMPILE_SYNTAX_MODULE = 'CTOR'

    def test_construct(self) -> None:
        test_data = ('one', 'two', 'three')
        for ctor in test_data:
            with self.subTest(ctor):
                # Given
                label = f"Lbl{ctor}'LParRParUnds'CTOR'Unds'Foo"
                pattern = CompositePattern(label)
                term = self.runtime.Term(pattern)

                # Then
                self.assertEqual(str(pattern), str(term))
