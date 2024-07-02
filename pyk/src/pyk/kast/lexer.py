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
    COLON = auto()
    KSEQ = auto()
    DOTK = auto()
    DOTKLIST = auto()
    TOKEN = auto()
    ID = auto()
    VARIABLE = auto()
    SORT = auto()
    KLABEL = auto()
    STRING = auto()


class Token(NamedTuple):
    text: str
    type: TokenType


class State(Enum):
    DEFAULT = auto()
    SORT = auto()


def lexer(text: Iterable[str]) -> Iterator[Token]:
    state = State.DEFAULT
    it = iter(text)
    la = next(it, '')
    while True:
        while la.isspace():
            la = next(it, '')

        if not la:
            yield _TOKENS[TokenType.EOF]
            return

        try:
            sublexer = _SUBLEXER[state][la]
        except KeyError:
            raise _unexpected_char(la) from None

        token, la = sublexer(la, it)
        state = _STATE.get(token.type, State.DEFAULT)
        yield token


_TOKENS: Final = {
    typ: Token(txt, typ)
    for typ, txt in (
        (TokenType.EOF, ''),
        (TokenType.LPAREN, '('),
        (TokenType.RPAREN, ')'),
        (TokenType.COMMA, ','),
        (TokenType.COLON, ':'),
        (TokenType.KSEQ, '~>'),
        (TokenType.DOTK, '.K'),
        (TokenType.DOTKLIST, '.KList'),
        (TokenType.TOKEN, '#token'),
    )
}


_DIGIT: Final = set('0123456789')
_LOWER: Final = set('abcdefghijklmnopqrstuvwxyz')
_UPPER: Final = set('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
_ALNUM: Final = set.union(_DIGIT, _LOWER, _UPPER)


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
    """Match an ID or token.

    Corresponds to regex: [#a-z](a-zA-Z0-9)*
    """
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
    r"""Match a variable.

    Corresponds to regex: _ | \?_ | \??_?[A-Z][a-zA-Z0-9'_]*
    """
    assert la == '?' or la == '_' or la in _UPPER

    # States:
    # 0: expect '_' or _UPPER
    # 1: continue if _UPPER
    # 2: read while _VARIABLE_CHARS
    state = {'?': 0, '_': 1}.get(la, 2)

    buf = [la]
    la = next(it, '')

    if state == 0:
        if la == '_':
            state = 1
        elif la in _UPPER:
            state = 2
        else:
            raise _unexpected_char(la)

        buf += la
        la = next(it, '')

    if state == 1:
        if la in _UPPER:
            buf += la
            la = next(it, '')
            state = 2
        else:
            la = next(it, '')
            text = ''.join(buf)
            return Token(text, TokenType.VARIABLE), la

    assert state == 2
    while la in _VARIABLE_CHARS:
        buf += la
        la = next(it, '')
    text = ''.join(buf)
    return Token(text, TokenType.VARIABLE), la


# For ease of implementation, KDOT and KDOTLIST tokens are read until _SEP
# This allows LA(1)
# But e.g. .KA won't be lexed, even though it can be read as [KDOT, VARIABLE]
_SEP: Final = set(',:()`"#.~ \t\r\n').union({''})


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


def _sort(la: str, it: Iterator[str]) -> tuple[Token, str]:
    assert la in _UPPER
    buf = [la]
    la = next(it, '')
    while la in _ALNUM:
        buf.append(la)
        la = next(it, '')
    text = ''.join(buf)
    return Token(text, TokenType.SORT), la


_SUBLEXER: Final[dict[State, dict[str, SubLexer]]] = {
    State.DEFAULT: {
        '(': _simple(_TOKENS[TokenType.LPAREN]),
        ')': _simple(_TOKENS[TokenType.RPAREN]),
        ',': _simple(_TOKENS[TokenType.COMMA]),
        ':': _simple(_TOKENS[TokenType.COLON]),
        '"': _delimited('"', TokenType.STRING),
        '`': _delimited('`', TokenType.KLABEL),
        '~': _kseq,
        '.': _dotk_or_dotklist,
        **{c: _id_or_token for c in {'#'}.union(_LOWER)},
        **{c: _variable for c in {'?', '_'}.union(_UPPER)},
    },
    State.SORT: {c: _sort for c in _UPPER},
}


_STATE: Final[dict[TokenType, State]] = {
    TokenType.COLON: State.SORT,
}
