from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm import parser
from pyk.kllvm.ast import Pattern
from pyk.kllvm.convert import pattern_to_llvm
from pyk.kore.parser import KoreParser
from pyk.testing import RuntimeTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.kllvm.runtime import Runtime

TEST_DATA = (
    '"foo"',
    'X : S',
    'X : SortInt{}',
    r'\dv{SortInt{}}("0")',
    'a{}()',
    'a{}(b{}())',
    r'\left-assoc{}(a{}(b1{}(), b2{}(), b3{}()))',
    r'\right-assoc{}(a{}(b1{}(), b2{}(), b3{}()))',
)


@pytest.mark.parametrize('kore_text', TEST_DATA)
def test_serialize(kore_text: str) -> None:
    # Given
    _pattern = KoreParser(kore_text).pattern()
    pattern = pattern_to_llvm(_pattern)

    # When
    bs = pattern.serialize()
    actual = Pattern.deserialize(bs)

    # Then
    assert actual is not None
    assert str(actual) == str(pattern)


class TestSerializeRaw(RuntimeTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    def test_serialize_raw(self, runtime: Runtime, tmp_path: Path) -> None:
        # Given
        kore_text = r"""Lbl'UndsPlus'Int'Unds'{}(\dv{SortInt{}}("1"),\dv{SortInt{}}("2"))"""
        pattern = parser.parse_pattern(kore_text)
        term = runtime.term(pattern)
        kore_file = tmp_path / 'kore'

        # When
        term._block._serialize_raw(str(kore_file), 'SortInt{}')
        pattern = Pattern.deserialize(kore_file.read_bytes())
        pattern_with_raw = Pattern.deserialize(kore_file.read_bytes(), strip_raw_term=False)

        # Then
        assert str(pattern) == r'\dv{SortInt{}}("3")'
        assert str(pattern_with_raw) == r'rawTerm{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("3")))'
