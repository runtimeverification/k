from dataclasses import dataclass
from enum import Enum, IntEnum, auto
from itertools import chain
from typing import Final, Iterator, List, Optional, Tuple, final


class StrLitLexer(Iterator[Tuple[str, 'StrLitLexer.TokenType']]):

    class TokenType(IntEnum):
        ASCII = 1
        ESC = 2
        UTF_8 = 3
        UTF_16 = 4
        UTF_32 = 5

    _iter: Iterator[Optional[str]]
    _la: Optional[str]

    def __init__(self, s: str):
        self._iter = iter(chain(s, [None]))
        self._la = next(self._iter)

    def __next__(self) -> Tuple[str, TokenType]:
        if self._la is None:
            raise StopIteration()

        if self._la == '"':
            raise ValueError('Unexpected character: "')

        if self._la == '\\':
            return self._escape_sequence()

        return self._printable_ascii_char()

    def _escape_sequence(self) -> Tuple[str, TokenType]:
        assert self._la is not None
        assert self._la == '\\'

        self._match('\\')

        if self._la in {'t', 'n', 'f', 'r', '"', '\\'}:
            token = f'\\{self._la}'
            self._consume()
            return token, self.TokenType.ESC

        hexa_params = {
            'x': (2, lambda x: None, self.TokenType.UTF_8),
            'u': (4, self._validate_utf_16, self.TokenType.UTF_16),
            'U': (8, self._validate_utf_32, self.TokenType.UTF_32),
        }

        if self._la in hexa_params:
            char = self._la
            self._consume()
            nr_digits, validate, token_type = hexa_params[char]
            hexa = self._match_hexa(nr_digits)
            validate(hexa)
            token = f'\\{char}{hexa}'
            return token, token_type

        raise ValueError(f'Unexpected character: {self._la}')

    @staticmethod
    def _validate_utf_16(hexa: str) -> None:
        if 0xD800 <= int(hexa, 16) <= 0xDFFF:
            raise ValueError(f'Illegal UTF-16 code point: {hexa}')

    @staticmethod
    def _validate_utf_32(hexa: str) -> None:
        StrLitLexer._validate_utf_16(hexa)

        if int(hexa, 16) > 0x10FFFF:
            raise ValueError(f'Illegal UTF-32 code point: {hexa}')

    def _printable_ascii_char(self) -> Tuple[str, TokenType]:
        assert self._la is not None
        assert self._la != '"'
        assert self._la != '\\'

        if not (32 <= ord(self._la) <= 126):
            raise ValueError(f'Expected printable ASCII character, found: character with code {ord(self._la)}')

        token = self._la
        self._consume()
        return token, self.TokenType.ASCII

    def _match(self, c: str) -> None:
        actual = '<EOF>' if self._la is None else self._la

        if self._la != c:
            raise ValueError(f'Expected {c}, found: {actual}')

        self._consume()

    def _consume(self) -> None:
        assert self._la is not None
        self._la = next(self._iter)

    def _match_hexa(self, length: int) -> str:
        if length < 0:
            raise ValueError(f'Expected nonnegative length, got: {length}')

        chars: List[str] = []
        for _ in range(length):
            actual = '<EOF>' if self._la is None else self._la

            if self._la not in set('0123456789abcdefABCDEF'):
                raise ValueError(f'Expected hexadecimal digit, found: {actual}')

            chars += self._la
            self._consume()

        return ''.join(chars)


@final
@dataclass(frozen=True)
class KoreToken:

    class Type(Enum):
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

    text: str
    type: Type


class KoreLexer(Iterator[KoreToken]):

    _KEYWORDS: Final = {
        'module': KoreToken.Type.KW_MODULE,
        'endmodule': KoreToken.Type.KW_ENDMODULE,
        'import': KoreToken.Type.KW_IMPORT,
        'sort': KoreToken.Type.KW_SORT,
        'hooked-sort': KoreToken.Type.KW_HOOKED_SORT,
        'symbol': KoreToken.Type.KW_SYMBOL,
        'hooked-symbol': KoreToken.Type.KW_HOOKED_SYMBOL,
        'axiom': KoreToken.Type.KW_AXIOM,
        'claim': KoreToken.Type.KW_CLAIM,
        'alias': KoreToken.Type.KW_ALIAS,
        'where': KoreToken.Type.KW_WHERE,
    }

    _SIMPLE_CHARS: Final = {
        ',': KoreToken.Type.COMMA,
        '(': KoreToken.Type.LPAREN,
        ')': KoreToken.Type.RPAREN,
        '{': KoreToken.Type.LBRACE,
        '}': KoreToken.Type.RBRACE,
        '[': KoreToken.Type.LBRACK,
        ']': KoreToken.Type.RBRACK,
    }

    # TODO Consider validating identifiers in kore.syntax with KoreLexer
    # TODO For this introduce a lexer mode that also emits WHITESPACE, {BLOCK, LINE}_COMMENT tokens
    # TODO Maybe StrLit lexer can also be moved to kore.lexer
    _ID_FIRST_CHARS: Final = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
    _ID_CHARS: Final = set("01234567890'-").union(_ID_FIRST_CHARS)
    _DELIMITERS: Final = set(':/').union(_SIMPLE_CHARS)

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
                return self._eof()

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

    def _eof(self) -> KoreToken:
        return KoreToken('', KoreToken.Type.EOF)

    def _simple_char(self) -> KoreToken:
        char = self._match(*self._SIMPLE_CHARS)
        return KoreToken(char, self._SIMPLE_CHARS[char])

    def _colon_or_walrus(self) -> KoreToken:
        self._match(':')

        if self._la == '=':
            self._consume()
            return KoreToken(':=', KoreToken.Type.WALRUS)

        return KoreToken(':', KoreToken.Type.COLON)

    def _string(self) -> KoreToken:
        buf: List[str] = []
        buf += self._match('"')
        while self._la != '"':
            if self._la == '\\':
                buf += self._consume()
            buf += self._consume()
        buf += self._consume()

        return KoreToken(''.join(buf), KoreToken.Type.STRING)

    def _symbol_id(self) -> KoreToken:
        self._match('\\')
        name = self._id_text()
        return KoreToken(f'\\{name}', KoreToken.Type.SYMBOL_ID)

    def _set_var_id(self) -> KoreToken:
        self._match('@')
        name = self._id_text()
        return KoreToken(f'@{name}', KoreToken.Type.SET_VAR_ID)

    def _id_or_keyword(self) -> KoreToken:
        name = self._id_text()

        if name in self._KEYWORDS:
            return KoreToken(name, self._KEYWORDS[name])

        return KoreToken(name, KoreToken.Type.ID)

    def _id_text(self) -> str:
        buf: List[str] = []
        buf += self._match(*self._ID_FIRST_CHARS)
        while self._la is not None and not self._la.isspace() and self._la not in self._DELIMITERS:
            buf += self._match(*self._ID_CHARS)
        return ''.join(buf)
