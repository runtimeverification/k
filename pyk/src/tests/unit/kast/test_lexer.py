from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.lexer import Token, TokenType, lexer

if TYPE_CHECKING:
    from typing import Final

TT: Final = TokenType
TEST_DATA: Final[tuple[tuple[str, list[Token]], ...]] = (
    ('', []),
    ('\n', []),
    ('(', [Token('(', TT.LPAREN)]),
    (')', [Token(')', TT.RPAREN)]),
    (',', [Token(',', TT.COMMA)]),
    ('~>', [Token('~>', TT.KSEQ)]),
    ('.K', [Token('.K', TT.DOTK)]),
    ('.KList', [Token('.KList', TT.DOTKLIST)]),
    ('``', [Token('``', TT.KLABEL)]),
    (r'`\x`', [Token(r'`\x`', TT.KLABEL)]),
    (r'`\``', [Token(r'`\``', TT.KLABEL)]),
    ('`foo`', [Token('`foo`', TT.KLABEL)]),
    ('""', [Token('""', TT.STRING)]),
    (r'"\x"', [Token(r'"\x"', TT.STRING)]),
    (r'"\""', [Token(r'"\""', TT.STRING)]),
    (r'"foo"', [Token('"foo"', TT.STRING)]),
    ('foo', [Token('foo', TT.ID)]),
    ('#foo', [Token('#foo', TT.ID)]),
    ('#token', [Token('#token', TT.TOKEN)]),
    ('fO0', [Token('fO0', TT.ID)]),
    ('_', [Token('_', TT.VARIABLE)]),
    ('A', [Token('A', TT.VARIABLE)]),
    (
        '`_+_`(#token("1", "Int"), X)',
        [
            Token('`_+_`', TT.KLABEL),
            Token('(', TT.LPAREN),
            Token('#token', TT.TOKEN),
            Token('(', TT.LPAREN),
            Token('"1"', TT.STRING),
            Token(',', TT.COMMA),
            Token('"Int"', TT.STRING),
            Token(')', TT.RPAREN),
            Token(',', TT.COMMA),
            Token('X', TT.VARIABLE),
            Token(')', TT.RPAREN),
        ],
    ),
)


@pytest.mark.parametrize('text,output', TEST_DATA, ids=[text for text, _ in TEST_DATA])
def test_lexer(text: str, output: list[str]) -> None:
    # Given
    expected = output + [Token('', TT.EOF)]

    # When
    actual = list(lexer(text))

    # Then
    assert actual == expected
