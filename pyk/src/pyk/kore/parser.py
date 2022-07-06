from dataclasses import dataclass
from enum import Enum, auto
from itertools import chain
from typing import Final, Iterator, List, Optional


class KoreLexer(Iterator['KoreLexer.Token']):

    class TokenType(Enum):
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
        KW_MODULE = auto()
        kW_ENDMODULE = auto()
        KW_IMPORT = auto()
        KW_SORT = auto()
        KW_HOOKED_SORT = auto()
        KW_SYMBOL = auto()
        KW_HOOKED_SYMBOL = auto()
        KW_AXIOM = auto
        KW_CLAIM = auto
        KW_ALIAS = auto
        KW_WHERE = auto

    @dataclass(frozen=True)
    class Token:
        text: str
        type: 'KoreLexer.TokenType'

    _KEYWORDS: Final = {
        'module': TokenType.KW_MODULE,
        'endmodule': TokenType.kW_ENDMODULE,
        'import': TokenType.KW_IMPORT,
        'sort': TokenType.KW_SORT,
        'hooked-sort': TokenType.KW_HOOKED_SORT,
        'symbol': TokenType.KW_SYMBOL,
        'hooked-symbol': TokenType.KW_HOOKED_SYMBOL,
        'axiom': TokenType.KW_AXIOM,
        'claim': TokenType.KW_CLAIM,
        'alias': TokenType.KW_ALIAS,
        'where': TokenType.KW_WHERE,
    }
    _SIMPLE_CHARS: Final = {
        ',': TokenType.COMMA,
        '(': TokenType.LPAREN,
        ')': TokenType.RPAREN,
        '{': TokenType.LBRACE,
        '}': TokenType.RBRACE,
        '[': TokenType.LBRACK,
        ']': TokenType.RBRACK,
    }
    _ID_FIRST_CHARS: Final = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
    _ID_CHARS: Final = set("01234567890'-").union(_ID_FIRST_CHARS)
    _DELIMITERS: Final = set(':/').union(_SIMPLE_CHARS)

    _iter: Iterator[Optional[str]]  # TODO maybe '' can be the sentinel
    _la: Optional[str]

    def __init__(self, s: str):
        self._iter = iter(chain(s, [None]))
        self._la = next(self._iter)

    def __next__(self) -> Token:
        while True:
            if self._la is None:
                raise StopIteration()

            if self._la.isspace():
                self._consume()
                continue

            if self._la == '/':
                self._comment()
                continue

            if self._la in self._SIMPLE_CHARS:
                return self._simple_char()

            if self._la == ':':
                return self._colon_or_walrus()

            if self._la == '"':
                return self._string()

            if self._la == '\\':
                return self._symbol_id()

            if self._la == '@':
                return self._set_var_id()

            if self._la in self._ID_FIRST_CHARS:
                return self._id_or_keyword()

            raise ValueError(f'Unexpected character: {self._la}')

    def _consume(self) -> str:
        if not self._la:
            raise ValueError('Unexpected <EOF>')

        consumed = self._la
        self._la = next(self._iter)
        return consumed

    # TODO _match() for sets of strings
    def _match(self, *cs: str) -> str:
        actual = '<EOF>' if self._la is None else self._la

        if self._la not in cs:
            expected = ', '.join(cs)
            raise ValueError(f'Expected {expected}, found: {actual}')

        return self._consume()

    def _comment(self) -> None:
        self._match('/')
        char = self._match('/', '*')

        if char == '/':
            self._line_comment_rest()
        elif char == '*':
            self._block_comment_rest()
        else:
            assert False

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

    def _simple_char(self) -> Token:
        char = self._match(*self._SIMPLE_CHARS)
        return self.Token(char, self._SIMPLE_CHARS[char])

    def _colon_or_walrus(self) -> Token:
        self._match(':')

        if self._la == '=':
            self._consume()
            return self.Token(':=', self.TokenType.WALRUS)

        return self.Token(':', self.TokenType.COLON)

    def _string(self) -> Token:
        buf: List[str] = []

        buf += self._match('"')
        while self._la != '"':
            buf += self._consume()
        buf += self._match('"')

        return self.Token(''.join(buf), self.TokenType.STRING)

    def _symbol_id(self) -> Token:
        self._match('\\')
        name = self._id_text()
        return self.Token(f'\\{name}', self.TokenType.SYMBOL_ID)

    def _set_var_id(self) -> Token:
        self._match('@')
        name = self._id_text()
        return self.Token(f'@{name}', self.TokenType.SET_VAR_ID)

    def _id_or_keyword(self) -> Token:
        name = self._id_text()

        if name in self._KEYWORDS:
            return self.Token(name, self._KEYWORDS[name])

        return self.Token(name, self.TokenType.ID)

    def _id_text(self) -> str:
        buf: List[str] = []
        buf += self._match(*self._ID_FIRST_CHARS)
        while self._la is not None and not self._la.isspace() and self._la not in self._DELIMITERS:
            buf += self._match(*self._ID_CHARS)
        return ''.join(buf)
