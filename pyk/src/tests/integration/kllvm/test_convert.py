from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.convert import kore_to_llvm, llvm_to_kore
from pyk.kore.parser import KoreParser

if TYPE_CHECKING:
    from typing import Final


TEST_DATA: Final = (
    ('string-printable', '"Hello World!"'),
    ('string-escape', r'"\t\n\r\f\\\""'),
    ('string-$', '"$"'),
    (r'string-\x24', r'"a\x24b"'),
    # (r'string-\u03b1', r'"a\u03b1b"'),
    # (r'string-\U0001F642', r'"a\U0001F642b"'),
    ('evar', 'X : SortInt{}'),
    ('evar-sortvar', 'X : S'),
    ('svar', '@X : SortInt{}'),
    ('svar-sortvar', '@X : S'),
    ('dv', r'\dv{SortInt{}}("1")'),
    ('top', r'\top{SortInt{}}()'),
    ('bottom', r'\bottom{SortInt{}}()'),
    ('and', r'\and{SortInt{}}(X : SortInt{}, \top{SortInt{}}())'),
    ('or', r'\or{SortInt{}}(X : SortInt{}, \bottom{SortInt{}}())'),
    ('implies', r'\implies{SortInt{}}(X : SortInt{}, Y :  SortInt{})'),
    ('iff', r'\iff{SortInt{}}(X : SortInt{}, Y :  SortInt{})'),
    ('exists', r'\exists{SortInt{}}(X : SortBool{}, \dv{SortInt{}}("0"))'),
    ('forall', r'\forall{SortInt{}}(X : SortBool{}, \dv{SortInt{}}("0"))'),
    ('mu', r'\mu{}(@X : SortBool{}, \dv{SortInt{}}("0"))'),
    ('nu', r'\nu{}(@X : SortBool{}, \dv{SortInt{}}("0"))'),
    ('ceil', r'\ceil{SortInt{}, SortGeneratedTopCell{}}(\dv{SortInt{}}("100"))'),
    ('floor', r'\floor{SortInt{}, SortGeneratedTopCell{}}(\dv{SortInt{}}("100"))'),
    ('equals', r'\equals{SortInt{}, SortGeneratedTopCell{}}(X : SortInt{}, \dv{SortInt{}}("100"))'),
    ('in', r'\in{SortInt{}, SortGeneratedTopCell{}}(X : SortInt{}, \dv{SortInt{}}("100"))'),
    ('next', r'\next{SortInt{}}(X : SortInt{})'),
    ('rewrites', r'\rewrites{SortInt{}}(X : SortInt{}, \dv{SortInt{}}("1"))'),
    ('app', r'foo{SortInt{}, S1, S2}(X : SortInt{}, \dv{SortInt{}}("1"))'),
    ('left-assoc', r'\left-assoc{}(foo{}(X : SortInt{}, Y :  SortInt{}, Z : SortInt{}))'),
    ('right-assoc', r'\right-assoc{}(foo{}(X : SortInt{}, Y :  SortInt{}, Z : SortInt{}))'),
)


@pytest.mark.parametrize('test_id,kore_text', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
def test_kore_to_llvm(test_id: str, kore_text: str) -> None:
    # Given
    expected = KoreParser(kore_text).pattern()

    # When
    kore_llvm = kore_to_llvm(expected)
    actual1 = KoreParser(str(kore_llvm)).pattern()

    # Then
    assert actual1 == expected

    # And when
    actual2 = llvm_to_kore(kore_llvm)

    # Then
    assert actual2 == expected
