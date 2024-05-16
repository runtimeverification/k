from __future__ import annotations

from collections.abc import Callable, Iterator
from enum import Enum, auto
from typing import TYPE_CHECKING, NamedTuple

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final


class TokenType(Enum):
    EOF = auto()
    LPAREN = auto()
    RPAREN = auto()
    COMMA = auto()
    KSEQ = auto()
    DOTK = auto()
    DOTKLIST = auto()
    TOKEN = auto()
    ID = auto()
    VARIABLE = auto()
    KLABEL = auto()
    STRING = auto()


class Token(NamedTuple):
    text: str
    type: TokenType


def lexer(text: Iterable[str]) -> Iterator[Token]:
    it = iter(text)
    la = next(it, '')
    while True:
        while la.isspace():
            la = next(it, '')

        if not la:
            yield _TOKENS[TokenType.EOF]
            return

        try:
            sublexer = _SUBLEXER[la]
        except KeyError:
            raise _unexpected_char(la) from None

        token, la = sublexer(la, it)
        yield token


_TOKENS: Final = {
    typ: Token(txt, typ)
    for typ, txt in (
        (TokenType.EOF, ''),
        (TokenType.LPAREN, '('),
        (TokenType.RPAREN, ')'),
        (TokenType.COMMA, ','),
        (TokenType.KSEQ, '~>'),
        (TokenType.DOTK, '.K'),
        (TokenType.DOTKLIST, '.KList'),
        (TokenType.TOKEN, '#token'),
    )
}


_DIGIT: Final = set('0123456789')
_LOWER: Final = set('abcdefghijklmnopqrstuvwxyz')
_UPPER: Final = set('ABCDEFGHIJKLMNOPQRSTUVWXYZ')


_UNEXPECTED_EOF: Final = ValueError('Unexpected end of file')


def _unexpected_char(actual: str, expected: str | None = None) -> ValueError:
    if expected is None:
        return ValueError(f'Unexpected character: {actual!r}')
    actual_str = repr(actual) if actual else '<EOF>'
    return ValueError(f'Expected {expected!r}, got: {actual_str}')


SubLexer = Callable[[str, Iterator[str]], tuple[Token, str]]


def _simple(token: Token) -> SubLexer:
    def sublexer(la: str, it: Iterator[str]) -> tuple[Token, str]:
        la = next(it, '')
        return token, la

    return sublexer


def _delimited(delimiter: str, type: TokenType) -> SubLexer:
    assert len(delimiter) == 1

    def sublexer(la: str, it: Iterator[str]) -> tuple[Token, str]:
        assert la == delimiter
        buf = [la]
        la = next(it, '')
        while True:
            if not la:
                raise _UNEXPECTED_EOF

            elif la == delimiter:
                buf.append(la)
                la = next(it, '')
                return Token(''.join(buf), type), la

            elif la == '\\':
                buf.append(la)
                la = next(it, '')
                if not la:
                    raise _UNEXPECTED_EOF
                buf.append(la)
                la = next(it, '')

            else:
                buf.append(la)
                la = next(it, '')

    return sublexer


def _kseq(la: str, it: Iterator[str]) -> tuple[Token, str]:
    assert la == '~'
    la = next(it, '')
    if la != '>':
        raise _unexpected_char(la, '>')
    la = next(it, '')
    return _TOKENS[TokenType.KSEQ], la


_ID_CHARS: Final = set.union(_LOWER, _UPPER, _DIGIT)


def _id_or_token(la: str, it: Iterator[str]) -> tuple[Token, str]:
    """[#a-z](a-zA-Z0-9)*"""
    assert la == '#' or la in _LOWER
    buf = [la]
    la = next(it, '')
    while la in _ID_CHARS:
        buf += la
        la = next(it, '')
    text = ''.join(buf)
    if text == '#token':
        return _TOKENS[TokenType.TOKEN], la
    return Token(text, TokenType.ID), la


_VARIABLE_CHARS: Final = set.union(_LOWER, _UPPER, _DIGIT, set("'_"))


def _variable(la: str, it: Iterator[str]) -> tuple[Token, str]:
    """_ | [A-Z][a-zA-Z0-9'_]*

    '_' is handled in a separate function.
    """
    assert la in _UPPER
    buf = [la]
    la = next(it, '')
    while la in _VARIABLE_CHARS:
        buf += la
        la = next(it, '')
    text = ''.join(buf)
    return Token(text, TokenType.VARIABLE), la


# For ease of implementation, KDOT and KDOTLIST tokens are read until _SEP
# This allows LA(1)
# But e.g. .KA won't be lexed, even though it can be read as [KDOT, VARIABLE]
_SEP: Final = set(',()`"#.~ \t\r\n').union({''})


def _dotk_or_dotklist(la: str, it: Iterator[str]) -> tuple[Token, str]:
    assert la == '.'
    la = next(it, '')
    if la != 'K':
        raise _unexpected_char(la, 'K')
    la = next(it, '')
    if la in _SEP:
        return _TOKENS[TokenType.DOTK], la
    for c in 'List':
        if la != c:
            raise _unexpected_char(la, c)
        la = next(it, '')
    if la in _SEP:
        return _TOKENS[TokenType.DOTKLIST], la
    raise _unexpected_char(la)


_SUBLEXER: Final[dict[str, SubLexer]] = {
    '(': _simple(_TOKENS[TokenType.LPAREN]),
    ')': _simple(_TOKENS[TokenType.RPAREN]),
    ',': _simple(_TOKENS[TokenType.COMMA]),
    '_': _simple(Token('_', TokenType.VARIABLE)),
    '"': _delimited('"', TokenType.STRING),
    '`': _delimited('`', TokenType.KLABEL),
    '~': _kseq,
    '.': _dotk_or_dotklist,
    **{c: _id_or_token for c in {'#'}.union(_LOWER)},
    **{c: _variable for c in _UPPER},
}
