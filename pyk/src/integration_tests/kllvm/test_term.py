from pyk.kllvm.ast import CompositePattern
from pyk.kllvm.runtime import compile_runtime, import_runtime

from .utils import RuntimeTest


class TermTest(RuntimeTest):
    KOMPILE_MAIN_FILE = 'k-files/ctor.k'
    KOMPILE_SYNTAX_MODULE = 'CTOR'

    def setUp(self) -> None:
        super().setUp()
        compile_runtime(self.kompiled_dir)
        self.runtime = import_runtime(self.kompiled_dir)

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
