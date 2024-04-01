from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer_lexer import (
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
    ('', [Token('', TokenType.EOF)], ''),
    (' ', [Token('', TokenType.EOF)], ''),
    ('//a', [Token('', TokenType.EOF)], ''),
    ('/*1*/', [Token('', TokenType.EOF)], ''),
    ('/*1*//*2*//*3*/', [Token('', TokenType.EOF)], ''),
    ('/*1*/ /*2*/ /*3*/rule', [Token('rule', TokenType.KW_RULE)], ''),
    ('/*1*/hello/*2*/rule', [Token('hello', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    (
        '/*1*/hello/*2*/world/*3*/rule',
        [Token('hello/*2*/world', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)],
        '',
    ),
    (
        '/*1*/hello/*2*/world/*3*/rule/*4*/',
        [Token('hello/*2*/world', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)],
        '',
    ),
    (
        ' /*1*/ hello /*2*/ world /*3*/ rule ',
        [Token('hello /*2*/ world', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)],
        ' ',
    ),
    (
        ' /*1*/ hello /*2*/ world /*3*/ rule /*4*/ ',
        [Token('hello /*2*/ world', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)],
        ' /*4*/ ',
    ),
    (
        'hello world // comment\nendmodule',
        [Token('hello world', TokenType.BUBBLE), Token('endmodule', TokenType.KW_ENDMODULE)],
        '',
    ),
    ('a //1\n/*2*/ rule', [Token('a', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    ('a //1\n/* rule */ rule', [Token('a', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    ('a', [Token('a', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('a/', [Token('a/', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('a/rule', [Token('a/rule', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('abc', [Token('abc', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('abc //', [Token('abc', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('abc /* 1 */ //', [Token('abc', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('rule', [Token('rule', TokenType.KW_RULE)], ''),
    ('rule/', [Token('rule/', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('rule//comment', [Token('rule', TokenType.KW_RULE)], ''),
    ('rule/*1*/', [Token('rule', TokenType.KW_RULE)], ''),
    ('a rule', [Token('a', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    ('arule', [Token('arule', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('a/**/rule', [Token('a', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    ('a/* comment */rule', [Token('a', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    ('an other rule', [Token('an other', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)], ''),
    (
        'cash rules everything around me',
        [Token('cash rules everything around me', TokenType.BUBBLE), Token('', TokenType.EOF)],
        '',
    ),
    (
        'cash rule/**/s everything around me',
        [Token('cash', TokenType.BUBBLE), Token('rule', TokenType.KW_RULE)],
        's everything around me',
    ),
    ('alias', [Token('alias', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('bubble alias', [Token('bubble alias', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('[', [Token('[', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('/**/[', [Token('[', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    ('[]', [Token('[]', TokenType.BUBBLE), Token('', TokenType.EOF)], ''),
    (
        '[a]:',
        [
            Token('[', TokenType.LBRACK),
            Token('a', TokenType.RULE_LABEL),
            Token(']', TokenType.RBRACK),
            Token(':', TokenType.COLON),
            Token('', TokenType.EOF),
        ],
        '',
    ),
    (
        '[a]:b',
        [
            Token('[', TokenType.LBRACK),
            Token('a', TokenType.RULE_LABEL),
            Token(']', TokenType.RBRACK),
            Token(':', TokenType.COLON),
            Token('b', TokenType.BUBBLE),
            Token('', TokenType.EOF),
        ],
        '',
    ),
    (
        '[klabel',
        [Token('[klabel', TokenType.BUBBLE), Token('', TokenType.EOF)],
        '',
    ),
    (
        '[klabel]',
        [
            Token('[', TokenType.LBRACK),
            Token('klabel', TokenType.ATTR_KEY),
            Token(']', TokenType.RBRACK),
            Token('', TokenType.EOF),
        ],
        '',
    ),
    (
        '[klabel(hello)]',
        [
            Token('[', TokenType.LBRACK),
            Token('klabel', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('hello', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
            Token('', TokenType.EOF),
        ],
        '',
    ),
    (
        'bubble [klabel(hello)]',
        [
            Token('bubble', TokenType.BUBBLE),
            Token('[', TokenType.LBRACK),
            Token('klabel', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('hello', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
            Token('', TokenType.EOF),
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
    it = iter(text)
    la = next(it, '')

    # When
    actual_tokens, la = _bubble_or_context(la, it)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_tokens == expected_tokens
    assert actual_remaining == expected_remaining


CONTEXT_TEST_DATA: Final = (
    ('alias', [Token('alias', TokenType.KW_ALIAS)], ''),
    ('bubble alias', [Token('bubble', TokenType.BUBBLE), Token('alias', TokenType.KW_ALIAS)], ''),
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
    it = iter(text)
    la = next(it, '')

    # When
    actual_tokens, la = _bubble_or_context(la, it, context=True)
    actual_remaining = la + ''.join(it)

    # Then
    assert actual_tokens == expected_tokens
    assert actual_remaining == expected_remaining


DEFAULT_TEST_DATA: Final = (
    ('', Token('', TokenType.EOF), ''),
    (' ', Token('', TokenType.EOF), ''),
    ('// comment', Token('', TokenType.EOF), ''),
    ('/* comment */', Token('', TokenType.EOF), ''),
    (' //', Token('', TokenType.EOF), ''),
    ('0', Token('0', TokenType.NAT), ''),
    ('01', Token('01', TokenType.NAT), ''),
    ('012abc', Token('012', TokenType.NAT), 'abc'),
    ('abc012', Token('abc012', TokenType.ID_LOWER), ''),
    ('#abc012', Token('#abc012', TokenType.ID_LOWER), ''),
    ('Abc012', Token('Abc012', TokenType.ID_UPPER), ''),
    ('#Abc012', Token('#Abc012', TokenType.ID_UPPER), ''),
    (':', Token(':', TokenType.COLON), ''),
    ('::=', Token('::=', TokenType.DCOLONEQ), ''),
    ('""', Token('""', TokenType.STRING), ''),
    ('"a"', Token('"a"', TokenType.STRING), ''),
    (r'"\n"', Token(r'"\n"', TokenType.STRING), ''),
    (r'"\""', Token(r'"\""', TokenType.STRING), ''),
    (r'"\\"', Token(r'"\\"', TokenType.STRING), ''),
    ('r', Token('r', TokenType.ID_LOWER), ''),
    ('r1', Token('r1', TokenType.ID_LOWER), ''),
    ('r""', Token('r""', TokenType.REGEX), ''),
    (r'r"\n"', Token(r'r"\n"', TokenType.REGEX), ''),
    (r'r"\""', Token(r'r"\""', TokenType.REGEX), ''),
    (r'r"\\"', Token(r'r"\\"', TokenType.REGEX), ''),
    ('rule', Token('rule', TokenType.KW_RULE), ''),
    ('rule0', Token('rule0', TokenType.ID_LOWER), ''),
    ('rulerule', Token('rulerule', TokenType.ID_LOWER), ''),
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
    ('private', Token('private', TokenType.KW_PRIVATE), ''),
    ('private MODULE', Token('private', TokenType.KW_PRIVATE), ' MODULE'),
    ('public', Token('public', TokenType.KW_PUBLIC), ''),
    ('module', Token('module', TokenType.MODNAME), ''),
    ('MODULE', Token('MODULE', TokenType.MODNAME), ''),
    ('module#module', Token('module', TokenType.MODNAME), '#module'),
    ('mo-du-le', Token('mo-du-le', TokenType.MODNAME), ''),
    ('m0-DU_l3', Token('m0-DU_l3', TokenType.MODNAME), ''),
    ('TEST-MODULE', Token('TEST-MODULE', TokenType.MODNAME), ''),
    ('TEST_MODULE', Token('TEST_MODULE', TokenType.MODNAME), ''),
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
    ('syntax', Token('syntax', TokenType.KW_SYNTAX), ''),
    ('syntaxx', Token('syntaxx', TokenType.KLABEL), ''),
    ('<foo()>', Token('<foo()>', TokenType.KLABEL), ''),
    ('>', Token('>', TokenType.GT), ''),
    ('>a', Token('>a', TokenType.KLABEL), ''),
    ('> a', Token('>', TokenType.GT), ' a'),
    ('/**/', Token('', TokenType.EOF), ''),
    ('a //', Token('a', TokenType.KLABEL), ' //'),
    ('// a', Token('', TokenType.EOF), ''),
    ('//a', Token('', TokenType.EOF), ''),
    ('/ a', Token('/', TokenType.KLABEL), ' a'),
    ('/a', Token('/a', TokenType.KLABEL), ''),
    ('/**/ a', Token('a', TokenType.KLABEL), ''),
    ('a /**/', Token('a', TokenType.KLABEL), ' /**/'),
    ('a/**/', Token('a/**/', TokenType.KLABEL), ''),
    ('/**/a', Token('/**/a', TokenType.KLABEL), ''),
    ('a/*1*//*2*/', Token('a/*1*//*2*/', TokenType.KLABEL), ''),
    ('/*1*//*2*/a', Token('/*1*//*2*/a', TokenType.KLABEL), ''),
    ('/*1*/a/*2*/', Token('/*1*/a/*2*/', TokenType.KLABEL), ''),
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
    ('a]', [Token('a', TokenType.ATTR_KEY), Token(']', TokenType.RBRACK)], ''),
    (' a ] ', [Token('a', TokenType.ATTR_KEY), Token(']', TokenType.RBRACK)], ' '),
    ('a<b>]', [Token('a<b>', TokenType.ATTR_KEY), Token(']', TokenType.RBRACK)], ''),
    ('1a-B<-->]', [Token('1a-B<-->', TokenType.ATTR_KEY), Token(']', TokenType.RBRACK)], ''),
    (
        'a()] ',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        ' ',
    ),
    (
        'a("")]',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('""', TokenType.STRING),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        '',
    ),
    (
        'a("hello")]',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('"hello"', TokenType.STRING),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        '',
    ),
    (
        'a( )] ',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token(' ', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        ' ',
    ),
    (
        'a(())] ',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('()', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        ' ',
    ),
    (
        'a(/*)] ',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('/*', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        ' ',
    ),
    (
        'a(()())] ',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('()()', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        ' ',
    ),
    (
        'a( tag content (()) () )]',
        [
            Token('a', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token(' tag content (()) () ', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
        ],
        '',
    ),
    (
        'a,b,c]',
        [
            Token('a', TokenType.ATTR_KEY),
            Token(',', TokenType.COMMA),
            Token('b', TokenType.ATTR_KEY),
            Token(',', TokenType.COMMA),
            Token('c', TokenType.ATTR_KEY),
            Token(']', TokenType.RBRACK),
        ],
        '',
    ),
    (
        ' /* 1 */ a /* 2 */ , b /* 3 */ ]',
        [
            Token('a', TokenType.ATTR_KEY),
            Token(',', TokenType.COMMA),
            Token('b', TokenType.ATTR_KEY),
            Token(']', TokenType.RBRACK),
        ],
        '',
    ),
    (
        'a<A>("hello"), b(foo(bar(%), baz))]',
        [
            Token('a<A>', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('"hello"', TokenType.STRING),
            Token(')', TokenType.RPAREN),
            Token(',', TokenType.COMMA),
            Token('b', TokenType.ATTR_KEY),
            Token('(', TokenType.LPAREN),
            Token('foo(bar(%), baz)', TokenType.ATTR_CONTENT),
            Token(')', TokenType.RPAREN),
            Token(']', TokenType.RBRACK),
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

            tokens.append(Token('\n'.join(token_lines), token_type))

        return tokens

    lines = path.read_text().splitlines()
    it = iter(lines)
    text = _text(it)
    tokens = _tokens(it)
    return text, tokens
