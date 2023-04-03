from __future__ import annotations

from enum import Enum, auto
from itertools import chain
from typing import TYPE_CHECKING, Iterator, NamedTuple

if TYPE_CHECKING:
    from typing import Final, Iterable, List, Optional


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


class KoreLexer(Iterator[KoreToken]):
    _EOF_TOKEN: Final = KoreToken('', TokenType.EOF)

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

    _ID_FIRST_CHARS: Final = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
    _ID_CHARS: Final = set("01234567890'-").union(_ID_FIRST_CHARS)

    _iter: Iterator[Optional[str]]  # TODO maybe '' can be the sentinel
    _la: Optional[str]
    _done: bool

    def __init__(self, s: str):
        self._iter = iter(chain(s, [None]))
        self._la = next(self._iter)
        self._done = False

    def __next__(self) -> KoreToken:
        while True:
            if self._la is None:
                if self._done:
                    raise StopIteration

                self._done = True
                return self._eof_token()

            if self._la.isspace():
                self._consume()
                continue

            if self._la == '/':
                self._comment()
                continue

            if self._la in self._SIMPLE_CHARS:
                return self._simple_char_token()

            if self._la in self._ID_FIRST_CHARS:
                return self._id_or_keyword_token()

            if self._la == '\\':
                return self._symbol_id_or_ml_symbol_token()

            if self._la == '@':
                return self._set_var_id_token()

            if self._la == ':':
                return self._colon_or_walrus_token()

            if self._la == '"':
                return self._string_token()

            raise ValueError(f'Unexpected character: {self._la}')

    def eof(self) -> None:
        self._eof_token()

    def id(self) -> str:
        name = self._id_text()
        if name in self._KEYWORDS:
            raise ValueError(f'Expected identifier, found keyword: {name}')
        return name

    def symbol_id(self) -> str:
        if self._la == '\\':
            return self._match('\\') + self._id_text()
        return self.id()

    def set_var_id(self) -> str:
        return self._match('@') + self._id_text()

    def _consume(self) -> str:
        if not self._la:
            raise ValueError('Unexpected <EOF>')

        consumed = self._la
        self._la = next(self._iter)
        return consumed

    def _match(self, c: str) -> str:
        if self._la != c:
            actual = '<EOF>' if self._la is None else self._la
            raise ValueError(f'Expected {c}, found: {actual}')

        return self._consume()

    def _match_any(self, cs: Iterable[str]) -> str:
        if self._la is None or self._la not in cs:
            expected = sorted(cs)
            actual = '<EOF>' if self._la is None else self._la
            raise ValueError(f'Expected {expected}, found: {actual}')

        return self._consume()

    def _comment(self) -> None:
        self._match('/')
        char = self._match_any({'/', '*'})

        if char == '/':
            self._line_comment_rest()
        elif char == '*':
            self._block_comment_rest()
        else:
            raise AssertionError()

    def _line_comment_rest(self) -> None:
        while self._la is not None and self._la != '\n':
            self._consume()

        if self._la:
            assert self._la == '\n'
            self._consume()

    def _block_comment_rest(self) -> None:
        while True:
            while self._la != '*':
                self._consume()

            self._consume()
            if self._la == '/':
                self._consume()
                break

    def _eof_token(self) -> KoreToken:
        if self._la is not None:
            raise ValueError(f'Expected <EOF>, found: {self._la}')
        return self._EOF_TOKEN

    def _simple_char_token(self) -> KoreToken:
        char = self._match_any(self._SIMPLE_CHARS)
        return self._SIMPLE_CHARS[char]

    def _colon_or_walrus_token(self) -> KoreToken:
        self._match(':')

        if self._la == '=':
            self._consume()
            return KoreToken(':=', TokenType.WALRUS)

        return KoreToken(':', TokenType.COLON)

    def _string_token(self) -> KoreToken:
        buf: List[str] = []
        buf += self._match('"')
        while self._la != '"':
            if self._la == '\\':
                buf += self._consume()
            buf += self._consume()
        buf += self._consume()

        return KoreToken(''.join(buf), TokenType.STRING)

    def _symbol_id_or_ml_symbol_token(self) -> KoreToken:
        self._match('\\')
        name = self._id_text()
        symbol_id = f'\\{name}'

        if symbol_id in self._ML_SYMBOLS:
            return self._ML_SYMBOLS[symbol_id]

        return KoreToken(symbol_id, TokenType.SYMBOL_ID)

    def _set_var_id_token(self) -> KoreToken:
        self._match('@')
        name = self._id_text()
        return KoreToken(f'@{name}', TokenType.SET_VAR_ID)

    def _id_or_keyword_token(self) -> KoreToken:
        name = self._id_text()

        if name in self._KEYWORDS:
            return self._KEYWORDS[name]

        return KoreToken(name, TokenType.ID)

    def _id_text(self) -> str:
        buf: List[str] = []
        buf += self._match_any(self._ID_FIRST_CHARS)
        while self._la in self._ID_CHARS:
            buf += self._consume()
        return ''.join(buf)
