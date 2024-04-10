from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer_lexer import (
    _INIT_LOC,
    Loc,
    LocationIterator,
    Token,
    TokenType,
    _attr,
    _bubble_or_context,
    _default,
    _klabel,
    _maybe_comment,
    _modname,
    outer_lexer,
)

from ..utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path
    from typing import Final


COMMENT_TEST_DATA: Final = (
    ('/', False, '/', ''),
    ('//', True, '//', ''),
    ('///', True, '///', ''),
    ('/*', False, '/*', ''),
    ('/**', False, '/**', ''),
    ('/**/', True, '/**/', ''),
    ('/* comment */', True, '/* comment */', ''),
    ('/**/ //', True, '/**/', ' //'),
    ('// /**/', True, '// /**/', ''),
)


@pytest.mark.parametrize(
    'text,expected_success,expected_consumed_text,expected_remaining',
    COMMENT_TEST_DATA,
    ids=[text for text, *_ in COMMENT_TEST_DATA],
)
def test_maybe_comment(
    text: str,
    expected_success: bool,
    expected_consumed_text: str,
    expected_remaining: str,
) -> None:
    # Given
    it = iter(text)
    la = next(it, '')
    expected_consumed = list(expected_consumed_text)

    # When
    actual_success, actual_consumed, la = _maybe_comment(la, it)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_success == expected_success
    assert actual_consumed == expected_consumed
    assert actual_remaining == expected_remaining


BUBBLE_TEST_DATA: Final = (
    ('', [Token('', TokenType.EOF, Loc(1, 0))], ''),
    (' ', [Token('', TokenType.EOF, Loc(1, 1))], ''),
    ('//a', [Token('', TokenType.EOF, Loc(1, 3))], ''),
    ('/*1*/', [Token('', TokenType.EOF, Loc(1, 5))], ''),
    ('/*1*//*2*//*3*/', [Token('', TokenType.EOF, Loc(1, 15))], ''),
    ('/*1*/ /*2*/ /*3*/rule', [Token('rule', TokenType.KW_RULE, Loc(1, 13))], ''),
    (
        '/*1*/hello/*2*/rule',
        [Token('hello', TokenType.BUBBLE, Loc(1, 6)), Token('rule', TokenType.KW_RULE, Loc(1, 16))],
        '',
    ),
    (
        '/*1*/hello/*2*/world/*3*/rule',
        [Token('hello/*2*/world', TokenType.BUBBLE, Loc(1, 6)), Token('rule', TokenType.KW_RULE, Loc(1, 26))],
        '',
    ),
    (
        '/*1*/hello/*2*/world/*3*/rule/*4*/',
        [Token('hello/*2*/world', TokenType.BUBBLE, Loc(1, 6)), Token('rule', TokenType.KW_RULE, Loc(1, 26))],
        '',
    ),
    (
        ' /*1*/ hello /*2*/ world /*3*/ rule ',
        [Token('hello /*2*/ world', TokenType.BUBBLE, Loc(1, 8)), Token('rule', TokenType.KW_RULE, Loc(1, 32))],
        ' ',
    ),
    (
        ' /*1*/ hello /*2*/ world /*3*/ rule /*4*/ ',
        [Token('hello /*2*/ world', TokenType.BUBBLE, Loc(1, 8)), Token('rule', TokenType.KW_RULE, Loc(1, 32))],
        ' /*4*/ ',
    ),
    (
        'hello world // comment\nendmodule',
        [Token('hello world', TokenType.BUBBLE, Loc(1, 1)), Token('endmodule', TokenType.KW_ENDMODULE, Loc(2, 1))],
        '',
    ),
    (
        'a //1\n/*2*/ rule',
        [Token('a', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(2, 7))],
        '',
    ),
    (
        'a //1\n/* rule */ rule',
        [Token('a', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(2, 12))],
        '',
    ),
    (
        'a',
        [Token('a', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 1))],
        '',
    ),
    (
        'a/',
        [Token('a/', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 2))],
        '',
    ),
    (
        'a/rule',
        [Token('a/rule', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 6))],
        '',
    ),
    (
        'abc',
        [Token('abc', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 3))],
        '',
    ),
    (
        'abc //',
        [Token('abc', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 6))],
        '',
    ),
    (
        'abc /* 1 */ //',
        [Token('abc', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 14))],
        '',
    ),
    ('rule', [Token('rule', TokenType.KW_RULE, Loc(1, 1))], ''),
    (
        'rule/',
        [Token('rule/', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 5))],
        '',
    ),
    ('rule//comment', [Token('rule', TokenType.KW_RULE, Loc(1, 1))], ''),
    ('rule/*1*/', [Token('rule', TokenType.KW_RULE, Loc(1, 1))], ''),
    (
        'a rule',
        [Token('a', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(1, 3))],
        '',
    ),
    (
        'arule',
        [Token('arule', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 5))],
        '',
    ),
    (
        'a/**/rule',
        [Token('a', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(1, 6))],
        '',
    ),
    (
        'a/* comment */rule',
        [Token('a', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(1, 15))],
        '',
    ),
    (
        'an other rule',
        [Token('an other', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(1, 10))],
        '',
    ),
    (
        'cash rules everything around me',
        [Token('cash rules everything around me', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 31))],
        '',
    ),
    (
        'cash rule/**/s everything around me',
        [Token('cash', TokenType.BUBBLE, Loc(1, 1)), Token('rule', TokenType.KW_RULE, Loc(1, 6))],
        's everything around me',
    ),
    (
        'alias',
        [Token('alias', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 5))],
        '',
    ),
    (
        'bubble alias',
        [Token('bubble alias', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 12))],
        '',
    ),
    (
        '[',
        [Token('[', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 1))],
        '',
    ),
    (
        '/**/[',
        [Token('[', TokenType.BUBBLE, Loc(1, 5)), Token('', TokenType.EOF, Loc(1, 5))],
        '',
    ),
    (
        '[]',
        [Token('[]', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 2))],
        '',
    ),
    (
        '[a]:',
        [
            Token('[', TokenType.LBRACK, Loc(1, 1)),
            Token('a', TokenType.RULE_LABEL, Loc(1, 2)),
            Token(']', TokenType.RBRACK, Loc(1, 3)),
            Token(':', TokenType.COLON, Loc(1, 4)),
            Token('', TokenType.EOF, Loc(1, 4)),
        ],
        '',
    ),
    (
        '[a]:b',
        [
            Token('[', TokenType.LBRACK, Loc(1, 1)),
            Token('a', TokenType.RULE_LABEL, Loc(1, 2)),
            Token(']', TokenType.RBRACK, Loc(1, 3)),
            Token(':', TokenType.COLON, Loc(1, 4)),
            Token('b', TokenType.BUBBLE, Loc(1, 5)),
            Token('', TokenType.EOF, Loc(1, 5)),
        ],
        '',
    ),
    (
        '[klabel',
        [Token('[klabel', TokenType.BUBBLE, Loc(1, 1)), Token('', TokenType.EOF, Loc(1, 7))],
        '',
    ),
    (
        '[klabel]',
        [
            Token('[', TokenType.LBRACK, Loc(1, 0)),
            Token('klabel', TokenType.ATTR_KEY, Loc(1, 0)),
            Token(']', TokenType.RBRACK, Loc(1, 0)),
            Token('', TokenType.EOF, Loc(1, 8)),
        ],
        '',
    ),
    (
        '[klabel(hello)]',
        [
            Token('[', TokenType.LBRACK, Loc(1, 0)),
            Token('klabel', TokenType.ATTR_KEY, Loc(1, 0)),
            Token('(', TokenType.LPAREN, Loc(1, 0)),
            Token('hello', TokenType.ATTR_CONTENT, Loc(1, 0)),
            Token(')', TokenType.RPAREN, Loc(1, 0)),
            Token(']', TokenType.RBRACK, Loc(1, 0)),
            Token('', TokenType.EOF, Loc(1, 15)),
        ],
        '',
    ),
    (
        'bubble [klabel(hello)]',
        [
            Token('bubble', TokenType.BUBBLE, Loc(1, 1)),
            Token('[', TokenType.LBRACK, Loc(1, 0)),
            Token('klabel', TokenType.ATTR_KEY, Loc(1, 0)),
            Token('(', TokenType.LPAREN, Loc(1, 0)),
            Token('hello', TokenType.ATTR_CONTENT, Loc(1, 0)),
            Token(')', TokenType.RPAREN, Loc(1, 0)),
            Token(']', TokenType.RBRACK, Loc(1, 0)),
            Token('', TokenType.EOF, Loc(1, 22)),
        ],
        '',
    ),
)


@pytest.mark.parametrize(
    'text,expected_tokens,expected_remaining',
    BUBBLE_TEST_DATA,
    ids=[text for text, *_ in BUBBLE_TEST_DATA],
)
def test_bubble(
    text: str,
    expected_tokens: list[Token],
    expected_remaining: str,
) -> None:
    # Given
    it = LocationIterator(text)
    la = next(it, '')

    # When
    actual_tokens, la = _bubble_or_context(la, it)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_tokens == expected_tokens
    assert actual_remaining == expected_remaining


CONTEXT_TEST_DATA: Final = (
    ('alias', [Token('alias', TokenType.KW_ALIAS, Loc(1, 1))], ''),
    ('bubble alias', [Token('bubble', TokenType.BUBBLE, Loc(1, 1)), Token('alias', TokenType.KW_ALIAS, Loc(1, 8))], ''),
)


@pytest.mark.parametrize(
    'text,expected_tokens,expected_remaining',
    CONTEXT_TEST_DATA,
    ids=[text for text, *_ in CONTEXT_TEST_DATA],
)
def test_context(
    text: str,
    expected_tokens: list[Token],
    expected_remaining: str,
) -> None:
    # Given
    it = LocationIterator(text)
    la = next(it, '')

    # When
    actual_tokens, la = _bubble_or_context(la, it, context=True)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_tokens == expected_tokens
    assert actual_remaining == expected_remaining


DEFAULT_TEST_DATA: Final = (
    ('', Token('', TokenType.EOF, Loc(1, 0)), ''),
    (' ', Token('', TokenType.EOF, Loc(1, 1)), ''),
    ('// comment', Token('', TokenType.EOF, Loc(1, 10)), ''),
    ('/* comment */', Token('', TokenType.EOF, Loc(1, 13)), ''),
    (' //', Token('', TokenType.EOF, Loc(1, 3)), ''),
    ('0', Token('0', TokenType.NAT, Loc(1, 1)), ''),
    ('01', Token('01', TokenType.NAT, Loc(1, 1)), ''),
    ('012abc', Token('012', TokenType.NAT, Loc(1, 1)), 'abc'),
    ('abc012', Token('abc012', TokenType.ID_LOWER, Loc(1, 1)), ''),
    ('#abc012', Token('#abc012', TokenType.ID_LOWER, Loc(1, 1)), ''),
    ('Abc012', Token('Abc012', TokenType.ID_UPPER, Loc(1, 1)), ''),
    ('#Abc012', Token('#Abc012', TokenType.ID_UPPER, Loc(1, 1)), ''),
    (':', Token(':', TokenType.COLON, Loc(1, 1)), ''),
    ('::=', Token('::=', TokenType.DCOLONEQ, Loc(1, 1)), ''),
    ('""', Token('""', TokenType.STRING, Loc(1, 1)), ''),
    ('"a"', Token('"a"', TokenType.STRING, Loc(1, 1)), ''),
    (r'"\n"', Token(r'"\n"', TokenType.STRING, Loc(1, 1)), ''),
    (r'"\""', Token(r'"\""', TokenType.STRING, Loc(1, 1)), ''),
    (r'"\\"', Token(r'"\\"', TokenType.STRING, Loc(1, 1)), ''),
    ('r', Token('r', TokenType.ID_LOWER, Loc(1, 1)), ''),
    ('r1', Token('r1', TokenType.ID_LOWER, Loc(1, 1)), ''),
    ('r""', Token('r""', TokenType.REGEX, Loc(1, 1)), ''),
    (r'r"\n"', Token(r'r"\n"', TokenType.REGEX, Loc(1, 1)), ''),
    (r'r"\""', Token(r'r"\""', TokenType.REGEX, Loc(1, 1)), ''),
    (r'r"\\"', Token(r'r"\\"', TokenType.REGEX, Loc(1, 1)), ''),
    ('rule', Token('rule', TokenType.KW_RULE, Loc(1, 1)), ''),
    ('rule0', Token('rule0', TokenType.ID_LOWER, Loc(1, 1)), ''),
    ('rulerule', Token('rulerule', TokenType.ID_LOWER, Loc(1, 1)), ''),
)


@pytest.mark.parametrize(
    'text,expected_token,expected_remaining',
    DEFAULT_TEST_DATA,
    ids=[text for text, *_ in DEFAULT_TEST_DATA],
)
def test_default(text: str, expected_token: Token, expected_remaining: str) -> None:
    # Given
    it = LocationIterator(text)
    la = next(it, '')

    # When
    actual_token, la = _default(la, it)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_token == expected_token
    assert actual_remaining == expected_remaining


MODNAME_TEST_DATA: Final = (
    ('private', Token('private', TokenType.KW_PRIVATE, Loc(1, 1)), ''),
    ('private MODULE', Token('private', TokenType.KW_PRIVATE, Loc(1, 1)), ' MODULE'),
    ('public', Token('public', TokenType.KW_PUBLIC, Loc(1, 1)), ''),
    ('module', Token('module', TokenType.MODNAME, Loc(1, 1)), ''),
    ('MODULE', Token('MODULE', TokenType.MODNAME, Loc(1, 1)), ''),
    ('module#module', Token('module', TokenType.MODNAME, Loc(1, 1)), '#module'),
    ('mo-du-le', Token('mo-du-le', TokenType.MODNAME, Loc(1, 1)), ''),
    ('m0-DU_l3', Token('m0-DU_l3', TokenType.MODNAME, Loc(1, 1)), ''),
    ('TEST-MODULE', Token('TEST-MODULE', TokenType.MODNAME, Loc(1, 1)), ''),
    ('TEST_MODULE', Token('TEST_MODULE', TokenType.MODNAME, Loc(1, 1)), ''),
)


@pytest.mark.parametrize(
    'text,expected_token,expected_remaining',
    MODNAME_TEST_DATA,
    ids=[text for text, *_ in MODNAME_TEST_DATA],
)
def test_modname(text: str, expected_token: Token, expected_remaining: str) -> None:
    # Given
    it = LocationIterator(text)
    la = next(it, '')

    # When
    actual_token, la = _modname(la, it)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_token == expected_token
    assert actual_remaining == expected_remaining


KLABEL_TEST_DATA: Final = (
    ('syntax', Token('syntax', TokenType.KW_SYNTAX, Loc(1, 1)), ''),
    ('syntaxx', Token('syntaxx', TokenType.KLABEL, Loc(1, 1)), ''),
    ('<foo()>', Token('<foo()>', TokenType.KLABEL, Loc(1, 1)), ''),
    ('>', Token('>', TokenType.GT, Loc(1, 1)), ''),
    ('>a', Token('>a', TokenType.KLABEL, Loc(1, 1)), ''),
    ('> a', Token('>', TokenType.GT, Loc(1, 1)), ' a'),
    ('/**/', Token('', TokenType.EOF, Loc(1, 4)), ''),
    ('a //', Token('a', TokenType.KLABEL, Loc(1, 1)), ' //'),
    ('// a', Token('', TokenType.EOF, Loc(1, 4)), ''),
    ('//a', Token('', TokenType.EOF, Loc(1, 3)), ''),
    ('/ a', Token('/', TokenType.KLABEL, Loc(1, 1)), ' a'),
    ('/a', Token('/a', TokenType.KLABEL, Loc(1, 1)), ''),
    ('/**/ a', Token('a', TokenType.KLABEL, Loc(1, 6)), ''),
    ('a /**/', Token('a', TokenType.KLABEL, Loc(1, 1)), ' /**/'),
    ('a/**/', Token('a/**/', TokenType.KLABEL, Loc(1, 1)), ''),
    ('/**/a', Token('/**/a', TokenType.KLABEL, Loc(1, 1)), ''),
    ('a/*1*//*2*/', Token('a/*1*//*2*/', TokenType.KLABEL, Loc(1, 1)), ''),
    ('/*1*//*2*/a', Token('/*1*//*2*/a', TokenType.KLABEL, Loc(1, 1)), ''),
    ('/*1*/a/*2*/', Token('/*1*/a/*2*/', TokenType.KLABEL, Loc(1, 1)), ''),
)


@pytest.mark.parametrize(
    'text,expected_token,expected_remaining',
    KLABEL_TEST_DATA,
    ids=[text for text, *_ in KLABEL_TEST_DATA],
)
def test_klabel(text: str, expected_token: Token, expected_remaining: str) -> None:
    # Given
    it = LocationIterator(text)
    la = next(it, '')

    # When
    actual_token, la = _klabel(la, it)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_token == expected_token
    assert actual_remaining == expected_remaining


ATTR_TEST_DATA: Final = (
    ('a]', [Token('a', TokenType.ATTR_KEY, _INIT_LOC), Token(']', TokenType.RBRACK, _INIT_LOC)], ''),
    (' a ] ', [Token('a', TokenType.ATTR_KEY, _INIT_LOC), Token(']', TokenType.RBRACK, _INIT_LOC)], ' '),
    ('a<b>]', [Token('a<b>', TokenType.ATTR_KEY, _INIT_LOC), Token(']', TokenType.RBRACK, _INIT_LOC)], ''),
    ('1a-B<-->]', [Token('1a-B<-->', TokenType.ATTR_KEY, _INIT_LOC), Token(']', TokenType.RBRACK, _INIT_LOC)], ''),
    (
        'a()] ',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        ' ',
    ),
    (
        'a("")]',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('""', TokenType.STRING, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        '',
    ),
    (
        'a("hello")]',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('"hello"', TokenType.STRING, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        '',
    ),
    (
        'a( )] ',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token(' ', TokenType.ATTR_CONTENT, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        ' ',
    ),
    (
        'a(())] ',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('()', TokenType.ATTR_CONTENT, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        ' ',
    ),
    (
        'a(/*)] ',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('/*', TokenType.ATTR_CONTENT, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        ' ',
    ),
    (
        'a(()())] ',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('()()', TokenType.ATTR_CONTENT, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        ' ',
    ),
    (
        'a( tag content (()) () )]',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token(' tag content (()) () ', TokenType.ATTR_CONTENT, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        '',
    ),
    (
        'a,b,c]',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token(',', TokenType.COMMA, _INIT_LOC),
            Token('b', TokenType.ATTR_KEY, _INIT_LOC),
            Token(',', TokenType.COMMA, _INIT_LOC),
            Token('c', TokenType.ATTR_KEY, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        '',
    ),
    (
        ' /* 1 */ a /* 2 */ , b /* 3 */ ]',
        [
            Token('a', TokenType.ATTR_KEY, _INIT_LOC),
            Token(',', TokenType.COMMA, _INIT_LOC),
            Token('b', TokenType.ATTR_KEY, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        '',
    ),
    (
        'a<A>("hello"), b(foo(bar(%), baz))]',
        [
            Token('a<A>', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('"hello"', TokenType.STRING, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(',', TokenType.COMMA, _INIT_LOC),
            Token('b', TokenType.ATTR_KEY, _INIT_LOC),
            Token('(', TokenType.LPAREN, _INIT_LOC),
            Token('foo(bar(%), baz)', TokenType.ATTR_CONTENT, _INIT_LOC),
            Token(')', TokenType.RPAREN, _INIT_LOC),
            Token(']', TokenType.RBRACK, _INIT_LOC),
        ],
        '',
    ),
)


@pytest.mark.parametrize(
    'text,expected_tokens,expected_remaining',
    ATTR_TEST_DATA,
    ids=[text for text, *_ in ATTR_TEST_DATA],
)
def test_attr(text: str, expected_tokens: list[Token], expected_remaining: str) -> None:
    # Given
    it = iter(text)
    la = next(it, '')
    attr_tokens = _attr(la, it)

    # When
    actual_tokens: list[Token] = []
    try:
        while True:
            actual_tokens.append(next(attr_tokens))
    except StopIteration as err:
        la = err.value

    actual_remaining = la + ''.join(it)

    # Then
    assert actual_tokens == expected_tokens
    assert actual_remaining == expected_remaining


LEXER_TEST_DATA_DIR: Final = TEST_DATA_DIR / 'outer-lexer'
LEXER_TEST_DATA: Final = tuple(LEXER_TEST_DATA_DIR.glob('*.test'))
assert LEXER_TEST_DATA


@pytest.mark.parametrize(
    'test_file',
    LEXER_TEST_DATA,
    ids=[test_file.stem for test_file in LEXER_TEST_DATA],
)
def test_lexer(test_file: Path) -> None:
    # Given
    text, expected_tokens = _parse(test_file)
    it = iter(text)

    # When
    actual_tokens = list(outer_lexer(it))
    remaining = next(it, None)

    # Then
    assert actual_tokens == expected_tokens
    assert remaining is None


def _parse(path: Path) -> tuple[str, list[Token]]:
    def _text(lines: Iterator[str]) -> str:
        text_lines: list[str] = []

        while True:
            line = next(lines)
            if line == '===':
                break
            text_lines.append(line)

        return '\n'.join(text_lines)

    def _tokens(lines: Iterator[str]) -> list[Token]:
        tokens: list[Token] = []

        line = next(lines)
        eof = False
        while not eof:
            token_lines: list[str] = []
            token_type = TokenType[line]

            line = next(lines)
            line_num, col = map(int, line.split(','))
            loc = Loc(line_num, col)

            line = next(lines)
            token_lines.append(line)

            maybe_type = False
            while True:
                opt_line = next(lines, None)
                if opt_line is None:
                    eof = True
                    break

                line = opt_line

                if line == '':
                    if maybe_type:
                        token_lines.append('')
                    maybe_type = True
                    continue

                if maybe_type:
                    if line in TokenType.__members__:
                        break

                    token_lines.append('')
                    maybe_type = False

                token_lines.append(line)

            tokens.append(Token('\n'.join(token_lines), token_type, loc))

        return tokens

    lines = path.read_text().splitlines()
    it = iter(lines)
    text = _text(it)
    tokens = _tokens(it)
    return text, tokens
