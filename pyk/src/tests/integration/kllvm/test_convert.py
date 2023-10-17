from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.convert import definition_to_llvm, llvm_to_definition, llvm_to_pattern, pattern_to_llvm
from pyk.kore.parser import KoreParser

if TYPE_CHECKING:
    from typing import Final


def _in_module(kore_text: str) -> str:
    return f'[] module FOO {kore_text} endmodule []'


PAT_TEST_DATA: Final = (
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

DEF_TEST_DATA: Final = (
    ('empty-modules', '[DefAttr{}("foo")] module FOO endmodule [ModAttr{}("bar")]'),
    ('import', '[] module FOO endmodule [] module BAR import FOO [ImportAttr{}()] endmodule []'),
    ('sort-decl', _in_module('sort Foo{S,T} [Attr{}()]')),
    ('hooked-sort-decl', _in_module('hooked-sort Foo{S,T} [Attr{}()]')),
    ('symbol-decl', _in_module('symbol Foo{S,T}(SortBar{S,T}, SortBaz{}) : SortInt [SymbolAttr{}()]')),
    ('hooked-symbol-decl', _in_module('hooked-symbol Foo{S,T}(SortBar{S,T}, SortBaz{}) : SortInt [SymbolAttr{}()]')),
    (
        'alias-decl',
        _in_module('alias Foo{S,T}(S) : T where Foo{S,T}(X : S) := X : T [AliasAttr{}()]'),
    ),
    ('axiom', _in_module(r'axiom {S} \rewrites{S}(X : S, \dv{SortInt{}}("1")) [AxiomAttr{}()]')),
    ('claim', _in_module(r'claim {S} \rewrites{S}(X : S, \dv{SortInt{}}("1")) [AxiomAttr{}()]')),
)


@pytest.mark.parametrize('test_id,kore_text', PAT_TEST_DATA, ids=[test_id for test_id, *_ in PAT_TEST_DATA])
def test_pattern_to_llvm(test_id: str, kore_text: str) -> None:
    # Given
    expected = KoreParser(kore_text).pattern()

    # When
    kore_llvm = pattern_to_llvm(expected)
    actual1 = KoreParser(str(kore_llvm)).pattern()

    # Then
    assert actual1 == expected

    # And when
    actual2 = llvm_to_pattern(kore_llvm)

    # Then
    assert actual2 == expected


@pytest.mark.parametrize('test_id,kore_text', DEF_TEST_DATA, ids=[test_id for test_id, *_ in DEF_TEST_DATA])
def test_definition_to_llvm(test_id: str, kore_text: str) -> None:
    # Given
    expected = KoreParser(kore_text).definition()

    # When
    kore_llvm = definition_to_llvm(expected)
    actual1 = KoreParser(str(kore_llvm)).definition()

    # Then
    assert actual1 == expected

    # And when
    actual2 = llvm_to_definition(kore_llvm)

    # Then
    assert actual2 == expected
