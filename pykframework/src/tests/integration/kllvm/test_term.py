from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pykframework.kllvm.load  # noqa: F401
from pykframework.kllvm.ast import CompositePattern
from pykframework.testing import RuntimeTest

if TYPE_CHECKING:
    from pykframework.kllvm.runtime import Runtime


class TestTerm(RuntimeTest):
    KOMPILE_DEFINITION = """
        module CTOR
            syntax Foo ::= one() | two() | three()
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'CTOR'
    KOMPILE_ARGS = {
        'syntax_module': 'CTOR',
    }

    @pytest.mark.parametrize('ctor', ('one', 'two', 'three'))
    def test_construct(self, runtime: Runtime, ctor: str) -> None:
        # Given
        label = f"Lbl{ctor}'LParRParUnds'CTOR'Unds'Foo"
        pattern = CompositePattern(label)
        term = runtime.term(pattern)

        # Then
        assert str(term) == str(pattern)
        assert str(term.pattern) == str(pattern)
        assert term.serialize() == pattern.serialize()
        assert str(runtime.deserialize(pattern.serialize())) == str(term)
