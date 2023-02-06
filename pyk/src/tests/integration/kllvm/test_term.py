from types import ModuleType

import pytest

from pyk.kllvm.ast import CompositePattern

from .utils import RuntimeTest


class TestTerm(RuntimeTest):
    KOMPILE_MAIN_FILE = 'k-files/ctor.k'
    KOMPILE_SYNTAX_MODULE = 'CTOR'

    @pytest.mark.parametrize('ctor', ('one', 'two', 'three'))
    def test_construct(self, runtime: ModuleType, ctor: str) -> None:
        # Given
        label = f"Lbl{ctor}'LParRParUnds'CTOR'Unds'Foo"
        pattern = CompositePattern(label)
        term = runtime.Term(pattern)

        # Then
        assert str(pattern) == str(term)
