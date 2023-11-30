from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.ast import CompositePattern
from pyk.testing import RuntimeTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kllvm.runtime import Runtime


class TestTerm(RuntimeTest):
    KOMPILE_MAIN_FILE = K_FILES / 'ctor.k'
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
