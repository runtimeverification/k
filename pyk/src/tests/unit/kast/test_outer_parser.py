from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer_parser import OuterParser
from pyk.kast.outer_syntax import (
    Alias,
    Assoc,
    Att,
    Claim,
    Config,
    Context,
    Definition,
    Import,
    Lexical,
    Module,
    NonTerminal,
    PriorityBlock,
    Production,
    Require,
    Rule,
    Sort,
    SortDecl,
    SyntaxAssoc,
    SyntaxDecl,
    SyntaxDefn,
    SyntaxLexical,
    SyntaxPriority,
    SyntaxSynonym,
    Terminal,
    UserList,
)

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast.outer_syntax import AST


SENTENCE_TEST_DATA: Final = (
    ('rule x', Rule('x')),
    ('rule [label]: x', Rule('x', label='label')),
    ('rule x [key1, key2(value)]', Rule('x', att=Att((('key1', ''), ('key2', 'value'))))),
    ('rule x [key("value")]', Rule('x', att=Att((('key', 'value'),)))),
    ('rule x [key("value\\n")]', Rule('x', att=Att((('key', 'value\n'),)))),
    (
        'rule [label]: x [key1, key2(value)]',
        Rule('x', label='label', att=Att((('key1', ''), ('key2', 'value')))),
    ),
    (
        'rule [label]: X => Y [key1, key2(value)]',
        Rule('X => Y', label='label', att=Att((('key1', ''), ('key2', 'value')))),
    ),
    ('claim x', Claim('x')),
    ('configuration x', Config('x')),
    ('context x', Context('x')),
    ('context alias x', Alias('x')),
    ('syntax lexical Digit = r"[0-9]"', SyntaxLexical('Digit', '[0-9]')),
    ('syntax left foo', SyntaxAssoc(Assoc.LEFT, ('foo',))),
    ('syntax right foo bar', SyntaxAssoc(Assoc.RIGHT, ('foo', 'bar'))),
    ('syntax non-assoc foo bar baz', SyntaxAssoc(Assoc.NON_ASSOC, ('foo', 'bar', 'baz'))),
    ('syntax priority foo', SyntaxPriority((('foo',),))),
    ('syntax priority foo bar', SyntaxPriority((('foo', 'bar'),))),
    ('syntax priority foo bar baz', SyntaxPriority((('foo', 'bar', 'baz'),))),
    ('syntax priority foo > bar', SyntaxPriority((('foo',), ('bar',)))),
    ('syntax priority foo > bar baz', SyntaxPriority((('foo',), ('bar', 'baz')))),
    ('syntax priority foo > bar > baz', SyntaxPriority((('foo',), ('bar',), ('baz',)))),
    ('syntax priority foo bar > baz', SyntaxPriority((('foo', 'bar'), ('baz',)))),
    ('syntax Foo', SyntaxDecl(SortDecl('Foo'))),
    ('syntax {Bar} Foo', SyntaxDecl(SortDecl('Foo', params=('Bar',)))),
    ('syntax {Bar, Baz} Foo', SyntaxDecl(SortDecl('Foo', params=('Bar', 'Baz')))),
    ('syntax Foo{Bar}', SyntaxDecl(SortDecl('Foo', args=('Bar',)))),
    ('syntax Foo{Bar, Baz}', SyntaxDecl(SortDecl('Foo', args=('Bar', 'Baz')))),
    ('syntax {Bar} Foo{Baz}', SyntaxDecl(SortDecl('Foo', params=('Bar',), args=('Baz',)))),
    ('syntax Foo [bar]', SyntaxDecl(SortDecl('Foo'), att=Att((('bar', ''),)))),
    ('syntax Foo [bar, baz]', SyntaxDecl(SortDecl('Foo'), att=Att((('bar', ''), ('baz', ''))))),
    (
        'syntax {Bar, Baz} Foo [bar, baz]',
        SyntaxDecl(SortDecl('Foo', params=('Bar', 'Baz')), Att((('bar', ''), ('baz', '')))),
    ),
    ('syntax Foo = Bar', SyntaxSynonym(SortDecl('Foo'), Sort('Bar'))),
    (
        'syntax {N} Vector{N} = Matrix{N, 1} [foo]',
        SyntaxSynonym(SortDecl('Vector', ('N',), ('N',)), Sort('Matrix', ('N', 1)), att=Att((('foo', ''),))),
    ),
    (
        'syntax Foo ::= r"foo" [token]',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Lexical('foo', att=Att((('token', ''),))),)),)),
    ),
    (
        'syntax Foos ::= List{Foo, ","}',
        SyntaxDefn(SortDecl('Foos'), (PriorityBlock((UserList('Foo', ',', non_empty=False),)),)),
    ),
    (
        'syntax Foos ::= NeList{Foo, ","}',
        SyntaxDefn(SortDecl('Foos'), (PriorityBlock((UserList('Foo', ',', non_empty=True),)),)),
    ),
    (
        'syntax Foo ::= "foo"',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((Terminal('foo'),)),)),)),
    ),
    (
        'syntax Foo ::= Bar',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((NonTerminal(Sort('Bar')),)),)),)),
    ),
    (
        'syntax Foo ::= Bar [bar]',
        SyntaxDefn(
            SortDecl('Foo'), (PriorityBlock((Production((NonTerminal(Sort('Bar')),), att=Att((('bar', ''),))),)),)
        ),
    ),
    (
        'syntax Foo ::= bar: Bar',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((NonTerminal(Sort('Bar'), 'bar'),)),)),)),
    ),
    (
        'syntax Foo ::= left: bar: Bar',
        SyntaxDefn(
            SortDecl('Foo'),
            (PriorityBlock((Production((NonTerminal(Sort('Bar'), 'bar'),)),), assoc=Assoc.LEFT),),
        ),
    ),
    (
        'syntax Foo ::= Bar: Baz',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((NonTerminal(Sort('Baz'), 'Bar'),)),)),)),
    ),
    (
        'syntax {N} Foo ::= Bar',
        SyntaxDefn(
            SortDecl('Foo', ('N',)),
            (PriorityBlock((Production((NonTerminal(Sort('Bar')),)),)),),
        ),
    ),
    (
        'syntax {Baz} Foo{Baz} ::= Bar{1, Baz}',
        SyntaxDefn(
            SortDecl('Foo', ('Baz',), ('Baz',)),
            (PriorityBlock((Production((NonTerminal(Sort('Bar', (1, 'Baz'))),)),)),),
        ),
    ),
    (
        'syntax Foo ::= left: "foo"',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((Terminal('foo'),)),), assoc=Assoc.LEFT),)),
    ),
    (
        'syntax Foo ::= right: "foo"',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((Terminal('foo'),)),), assoc=Assoc.RIGHT),)),
    ),
    (
        'syntax Foo ::= non-assoc: "foo"',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((Terminal('foo'),)),), assoc=Assoc.NON_ASSOC),)),
    ),
    (
        'syntax Foo ::= "bar" Bar',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((Terminal('bar'), NonTerminal(Sort('Bar')))),)),)),
    ),
    (
        'syntax Foo ::= "bar" | Bar',
        SyntaxDefn(
            SortDecl('Foo'),
            (PriorityBlock((Production((Terminal('bar'),)), Production((NonTerminal(Sort('Bar')),)))),),
        ),
    ),
    (
        'syntax Foo ::= "bar" > "baz"',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock((Production((Terminal('bar'),)),)),
                PriorityBlock((Production((Terminal('baz'),)),)),
            ),
        ),
    ),
    (
        'syntax Foo ::= "bar" Bar > "baz" Baz',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock((Production((Terminal('bar'), NonTerminal(Sort('Bar')))),)),
                PriorityBlock((Production((Terminal('baz'), NonTerminal(Sort('Baz')))),)),
            ),
        ),
    ),
    (
        'syntax Foo ::= "bar" | Bar > "baz" | Baz',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock((Production((Terminal('bar'),)), Production((NonTerminal(Sort('Bar')),)))),
                PriorityBlock((Production((Terminal('baz'),)), Production((NonTerminal(Sort('Baz')),)))),
            ),
        ),
    ),
    (
        'syntax Foo ::= left: "bar" | Bar > right: "baz" | Baz',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock(
                    (Production((Terminal('bar'),)), Production((NonTerminal(Sort('Bar')),))), assoc=Assoc.LEFT
                ),
                PriorityBlock(
                    (Production((Terminal('baz'),)), Production((NonTerminal(Sort('Baz')),))), assoc=Assoc.RIGHT
                ),
            ),
        ),
    ),
    (
        'syntax Foos ::= left: "bar" | Bar > right: r"baz" [token] > non-assoc: List{Foo, ","}',
        SyntaxDefn(
            SortDecl('Foos'),
            (
                PriorityBlock(
                    (Production((Terminal('bar'),)), Production((NonTerminal(Sort('Bar')),))),
                    assoc=Assoc.LEFT,
                ),
                PriorityBlock((Lexical('baz', att=Att((('token', ''),))),), assoc=Assoc.RIGHT),
                PriorityBlock((UserList('Foo', ','),), assoc=Assoc.NON_ASSOC),
            ),
        ),
    ),
    (
        'syntax Foo ::= foo()',
        SyntaxDefn(SortDecl('Foo'), (PriorityBlock((Production((Terminal('foo'), Terminal('('), Terminal(')'))),)),)),
    ),
    (
        'syntax Foo ::= foo() | bar()',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock(
                    (
                        Production((Terminal('foo'), Terminal('('), Terminal(')'))),
                        Production((Terminal('bar'), Terminal('('), Terminal(')'))),
                    )
                ),
            ),
        ),
    ),
    (
        'syntax Foo ::= foo() | bar() | baz()',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock(
                    (
                        Production((Terminal('foo'), Terminal('('), Terminal(')'))),
                        Production((Terminal('bar'), Terminal('('), Terminal(')'))),
                        Production((Terminal('baz'), Terminal('('), Terminal(')'))),
                    )
                ),
            ),
        ),
    ),
    (
        'syntax Foo ::= foo(Bar)',
        SyntaxDefn(
            SortDecl('Foo'),
            (PriorityBlock((Production((Terminal('foo'), Terminal('('), NonTerminal(Sort('Bar')), Terminal(')'))),)),),
        ),
    ),
    (
        'syntax Foo ::= foo(bar: Bar)',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock(
                    (Production((Terminal('foo'), Terminal('('), NonTerminal(Sort('Bar'), 'bar'), Terminal(')'))),)
                ),
            ),
        ),
    ),
    (
        'syntax Foo ::= foo(Bar, Baz)',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock(
                    (
                        Production(
                            (
                                Terminal('foo'),
                                Terminal('('),
                                NonTerminal(Sort('Bar')),
                                Terminal(','),
                                NonTerminal(Sort('Baz')),
                                Terminal(')'),
                            )
                        ),
                    )
                ),
            ),
        ),
    ),
    (
        'syntax Foo ::= foo(bar: Bar, baz: Baz)',
        SyntaxDefn(
            SortDecl('Foo'),
            (
                PriorityBlock(
                    (
                        Production(
                            (
                                Terminal('foo'),
                                Terminal('('),
                                NonTerminal(Sort('Bar'), 'bar'),
                                Terminal(','),
                                NonTerminal(Sort('Baz'), 'baz'),
                                Terminal(')'),
                            )
                        ),
                    )
                ),
            ),
        ),
    ),
    (
        'syntax List [hook(LIST.List)]',
        SyntaxDecl(SortDecl('List'), att=Att((('hook', 'LIST.List'),))),
    ),
    (
        'syntax List ::= List List',
        SyntaxDefn(
            SortDecl('List'), (PriorityBlock((Production((NonTerminal(Sort('List')), NonTerminal(Sort('List')))),)),)
        ),
    ),
    (
        'syntax KItem ::= List "[" Int "]"',
        SyntaxDefn(
            SortDecl('KItem'),
            (
                PriorityBlock(
                    (Production((NonTerminal(Sort('List')), Terminal('['), NonTerminal(Sort('Int')), Terminal(']'))),)
                ),
            ),
        ),
    ),
)


@pytest.mark.parametrize('k_text,expected', SENTENCE_TEST_DATA, ids=[k_text for k_text, _ in SENTENCE_TEST_DATA])
def test_sentence(k_text: str, expected: AST) -> None:
    # Given
    parser = OuterParser(k_text)

    # When
    actual = parser.sentence()

    # Then
    assert actual == expected


IMPORT_TEST_DATA: Final = (
    ('imports TEST', Import('TEST', public=True)),
    ('imports public TEST', Import('TEST', public=True)),
    ('imports private TEST', Import('TEST', public=False)),
)


@pytest.mark.parametrize('k_text,expected', IMPORT_TEST_DATA, ids=[k_text for k_text, _ in IMPORT_TEST_DATA])
def test_import(k_text: str, expected: AST) -> None:
    # Given
    parser = OuterParser(k_text)

    # When
    actual = parser.importt()

    # Then
    assert actual == expected


MODULE_TEST_DATA: Final = (
    ('module FOO endmodule', Module('FOO')),
    ('module FOO [foo] endmodule', Module('FOO', att=Att((('foo', ''),)))),
    ('module FOO imports BAR endmodule', Module('FOO', imports=(Import('BAR'),))),
    ('module FOO imports BAR imports BAZ endmodule', Module('FOO', imports=(Import('BAR'), Import('BAZ')))),
    ('module FOO rule x endmodule', Module('FOO', sentences=(Rule('x'),))),
    ('module FOO rule x rule y endmodule', Module('FOO', sentences=(Rule('x'), Rule('y')))),
    (
        'module FOO [foo] imports BAR rule x endmodule',
        Module('FOO', sentences=(Rule('x'),), imports=(Import('BAR'),), att=Att((('foo', ''),))),
    ),
)


@pytest.mark.parametrize('k_text,expected', MODULE_TEST_DATA, ids=[k_text for k_text, _ in MODULE_TEST_DATA])
def test_module(k_text: str, expected: AST) -> None:
    # Given
    parser = OuterParser(k_text)

    # When
    actual = parser.module()

    # Then
    assert actual == expected


def test_require() -> None:
    # Given
    k_text = 'requires "foo.k"'
    parser = OuterParser(k_text)
    expected = Require('foo.k')

    # When
    actual = parser.require()

    # Then
    assert actual == expected


DEFINITION_TEST_DATA: Final = (
    ('', Definition()),
    ('requires "foo.k"', Definition(requires=(Require('foo.k'),))),
    ('requires "foo.k" requires "bar.k"', Definition(requires=(Require('foo.k'), Require('bar.k')))),
    ('module FOO endmodule', Definition(modules=(Module('FOO'),))),
    ('module FOO endmodule module BAR endmodule', Definition(modules=(Module('FOO'), Module('BAR')))),
    ('requires "foo.k" module FOO endmodule', Definition(modules=(Module('FOO'),), requires=(Require('foo.k'),))),
)


@pytest.mark.parametrize('k_text,expected', DEFINITION_TEST_DATA, ids=[k_text for k_text, _ in DEFINITION_TEST_DATA])
def test_definition(k_text: str, expected: AST) -> None:
    # Given
    parser = OuterParser(k_text)

    # When
    actual = parser.definition()

    # Then
    assert actual == expected
