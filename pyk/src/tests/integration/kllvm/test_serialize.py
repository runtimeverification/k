import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.ast import Pattern
from pyk.kllvm.convert import pattern_to_llvm
from pyk.kore.parser import KoreParser

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
