from __future__ import annotations

from enum import Enum, auto
from typing import TYPE_CHECKING, NamedTuple

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator, Mapping
    from typing import Final


class TokenType(Enum):
    EOF = 0
    COMMA = auto()
    COLON = auto()
    WALRUS = auto()
    LPAREN = auto()
    RPAREN = auto()
    LBRACE = auto()
    RBRACE = auto()
    LBRACK = auto()
    RBRACK = auto()
    STRING = auto()
    ID = auto()
    SYMBOL_ID = auto()
    SET_VAR_ID = auto()
    ML_TOP = auto()
    ML_BOTTOM = auto()
    ML_NOT = auto()
    ML_AND = auto()
    ML_OR = auto()
    ML_IMPLIES = auto()
    ML_IFF = auto()
    ML_EXISTS = auto()
    ML_FORALL = auto()
    ML_MU = auto()
    ML_NU = auto()
    ML_CEIL = auto()
    ML_FLOOR = auto()
    ML_EQUALS = auto()
    ML_IN = auto()
    ML_NEXT = auto()
    ML_REWRITES = auto()
    ML_DV = auto()
    ML_LEFT_ASSOC = auto()
    ML_RIGHT_ASSOC = auto()
    KW_MODULE = auto()
    KW_ENDMODULE = auto()
    KW_IMPORT = auto()
    KW_SORT = auto()
    KW_HOOKED_SORT = auto()
    KW_SYMBOL = auto()
    KW_HOOKED_SYMBOL = auto()
    KW_AXIOM = auto()
    KW_CLAIM = auto()
    KW_ALIAS = auto()
    KW_WHERE = auto()


class KoreToken(NamedTuple):
    text: str
    type: TokenType


_EOF_TOKEN: Final = KoreToken('', TokenType.EOF)
_COLON_TOKEN: Final = KoreToken(':', TokenType.COLON)
_WALRUS_TOKEN: Final = KoreToken(':=', TokenType.WALRUS)

_ML_SYMBOLS: Final = {
    r'\top': KoreToken(r'\top', TokenType.ML_TOP),
    r'\bottom': KoreToken(r'\bottom', TokenType.ML_BOTTOM),
    r'\not': KoreToken(r'\not', TokenType.ML_NOT),
    r'\and': KoreToken(r'\and', TokenType.ML_AND),
    r'\or': KoreToken(r'\or', TokenType.ML_OR),
    r'\implies': KoreToken(r'\implies', TokenType.ML_IMPLIES),
    r'\iff': KoreToken(r'\iff', TokenType.ML_IFF),
    r'\exists': KoreToken(r'\exists', TokenType.ML_EXISTS),
    r'\forall': KoreToken(r'\forall', TokenType.ML_FORALL),
    r'\mu': KoreToken(r'\mu', TokenType.ML_MU),
    r'\nu': KoreToken(r'\nu', TokenType.ML_NU),
    r'\ceil': KoreToken(r'\ceil', TokenType.ML_CEIL),
    r'\floor': KoreToken(r'\floor', TokenType.ML_FLOOR),
    r'\equals': KoreToken(r'\equals', TokenType.ML_EQUALS),
    r'\in': KoreToken(r'\in', TokenType.ML_IN),
    r'\next': KoreToken(r'\next', TokenType.ML_NEXT),
    r'\rewrites': KoreToken(r'\rewrites', TokenType.ML_REWRITES),
    r'\dv': KoreToken(r'\dv', TokenType.ML_DV),
    r'\left-assoc': KoreToken(r'\left-assoc', TokenType.ML_LEFT_ASSOC),
    r'\right-assoc': KoreToken(r'\right-assoc', TokenType.ML_RIGHT_ASSOC),
}

_KEYWORDS: Final = {
    'module': KoreToken('module', TokenType.KW_MODULE),
    'endmodule': KoreToken('endmodule', TokenType.KW_ENDMODULE),
    'import': KoreToken('import', TokenType.KW_IMPORT),
    'sort': KoreToken('sort', TokenType.KW_SORT),
    'hooked-sort': KoreToken('hooked-sort', TokenType.KW_HOOKED_SORT),
    'symbol': KoreToken('symbol', TokenType.KW_SYMBOL),
    'hooked-symbol': KoreToken('hooked-symbol', TokenType.KW_HOOKED_SYMBOL),
    'axiom': KoreToken('axiom', TokenType.KW_AXIOM),
    'claim': KoreToken('claim', TokenType.KW_CLAIM),
    'alias': KoreToken('alias', TokenType.KW_ALIAS),
    'where': KoreToken('where', TokenType.KW_WHERE),
}

_SIMPLE_CHARS: Final = {
    ',': KoreToken(',', TokenType.COMMA),
    '(': KoreToken('(', TokenType.LPAREN),
    ')': KoreToken(')', TokenType.RPAREN),
    '{': KoreToken('{', TokenType.LBRACE),
    '}': KoreToken('}', TokenType.RBRACE),
    '[': KoreToken('[', TokenType.LBRACK),
    ']': KoreToken(']', TokenType.RBRACK),
}

_WHITESPACE_CHARS: Final = {' ', '\t', '\n', '\r'}
_ID_FIRST_CHARS: Final = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
_ID_CHARS: Final = set("01234567890'-").union(_ID_FIRST_CHARS)


def _whitespace(la: str, it: Iterator[str]) -> tuple[str, None]:
    la = next(it, '')
    while la in _WHITESPACE_CHARS:
        la = next(it, '')
    return la, None


def _comment(la: str, it: Iterator[str]) -> tuple[str, None]:
    # line comment
    la = next(it, '')
    if la == '/':
        while la and la != '\n':
            la = next(it, '')
        if la:
            la = next(it, '')

    # block comment
    elif la == '*':
        la = next(it)
        while True:
            while la != '*':
                la = next(it)
            la = next(it)
            if la == '/':
                la = next(it, '')
                break

    # mismatch
    else:
        raise ValueError(f'Expected / or *, got: {la}')

    return la, None


def _simple_char(la: str, it: Iterator[str]) -> tuple[str, KoreToken]:
    return next(it, ''), _SIMPLE_CHARS[la]


def _colon_or_walrus(la: str, it: Iterator[str]) -> tuple[str, KoreToken]:
    la = next(it, '')
    if la == '=':
        token = _WALRUS_TOKEN
        la = next(it, '')
    else:
        token = _COLON_TOKEN
    return la, token


def _id_or_keyword(la: str, it: Iterator[str]) -> tuple[str, KoreToken]:
    buf = [la]
    la = next(it, '')
    while la in _ID_CHARS:
        buf.append(la)
        la = next(it, '')
    name = ''.join(buf)
    if name in _KEYWORDS:
        token = _KEYWORDS[name]
    else:
        token = KoreToken(name, TokenType.ID)
    return la, token


def _symbol_or_ml_conn(la: str, it: Iterator[str]) -> tuple[str, KoreToken]:
    buf = [la]
    la = next(it)
    if la not in _ID_FIRST_CHARS:
        raise ValueError(f'Expected letter, got: {la}')
    buf.append(la)
    la = next(it, '')
    while la in _ID_CHARS:
        buf.append(la)
        la = next(it, '')
    symbol = ''.join(buf)
    if symbol in _ML_SYMBOLS:
        token = _ML_SYMBOLS[symbol]
    else:
        token = KoreToken(symbol, TokenType.SYMBOL_ID)
    return la, token


def _set_var_id(la: str, it: Iterator[str]) -> tuple[str, KoreToken]:
    buf = [la]
    la = next(it)
    if la not in _ID_FIRST_CHARS:
        raise ValueError(f'Expected letter, got: {la}')
    buf.append(la)
    la = next(it, '')
    while la in _ID_CHARS:
        buf.append(la)
        la = next(it, '')
    return la, KoreToken(''.join(buf), TokenType.SET_VAR_ID)


def _string(la: str, it: Iterator[str]) -> tuple[str, KoreToken]:
    buf = [la]
    la = next(it)
    while la != '"':
        if la == '\\':
            buf.append(la)
            la = next(it)
        buf.append(la)
        la = next(it)
    buf.append(la)
    return next(it, ''), KoreToken(''.join(buf), TokenType.STRING)


_DISPATCH_TABLE: Final[Mapping[str, Callable[[str, Iterator[str]], tuple[str, KoreToken | None]]]] = {
    '/': _comment,
    ':': _colon_or_walrus,
    '"': _string,
    '@': _set_var_id,
    '\\': _symbol_or_ml_conn,
    **{c: _whitespace for c in _WHITESPACE_CHARS},
    **{c: _id_or_keyword for c in _ID_FIRST_CHARS},
    **{c: _simple_char for c in _SIMPLE_CHARS},
}


def kore_lexer(it: Iterable[str]) -> Iterator[KoreToken]:
    it = iter(it)
    la = next(it, '')
    while True:
        if not la:
            yield _EOF_TOKEN
            return

        try:
            next_state = _DISPATCH_TABLE[la]
        except KeyError as err:
            raise ValueError(f'Unexpected character: {la}') from err

        try:
            la, token = next_state(la, it)
            if token:
                yield token
        except StopIteration as err:
            raise ValueError('Unexpected end of file') from err
