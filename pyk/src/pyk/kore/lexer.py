from dataclasses import dataclass
from enum import Enum, IntEnum, auto
from itertools import chain
from typing import Final, Iterable, Iterator, List, Optional, Tuple, final


class KoreStringLexer(Iterator[Tuple[str, 'KoreStringLexer.TokenType']]):
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

    def _match(self, c: str) -> None:
        actual = '<EOF>' if self._la is None else self._la

        if self._la != c:
            raise ValueError(f'Expected {c}, found: {actual}')

        self._consume()

    def _consume(self) -> None:
        assert self._la is not None
        self._la = next(self._iter)

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
            hexa = self._hexa(nr_digits)
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
        KoreStringLexer._validate_utf_16(hexa)

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

    def _hexa(self, length: int) -> str:
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

    text: str
    type: Type


class KoreLexer(Iterator[KoreToken]):
    _EOF_TOKEN: Final = KoreToken('', KoreToken.Type.EOF)

    _ML_SYMBOLS: Final = {
        r'\top': KoreToken(r'\top', KoreToken.Type.ML_TOP),
        r'\bottom': KoreToken(r'\bottom', KoreToken.Type.ML_BOTTOM),
        r'\not': KoreToken(r'\not', KoreToken.Type.ML_NOT),
        r'\and': KoreToken(r'\and', KoreToken.Type.ML_AND),
        r'\or': KoreToken(r'\or', KoreToken.Type.ML_OR),
        r'\implies': KoreToken(r'\implies', KoreToken.Type.ML_IMPLIES),
        r'\iff': KoreToken(r'\iff', KoreToken.Type.ML_IFF),
        r'\exists': KoreToken(r'\exists', KoreToken.Type.ML_EXISTS),
        r'\forall': KoreToken(r'\forall', KoreToken.Type.ML_FORALL),
        r'\mu': KoreToken(r'\mu', KoreToken.Type.ML_MU),
        r'\nu': KoreToken(r'\nu', KoreToken.Type.ML_NU),
        r'\ceil': KoreToken(r'\ceil', KoreToken.Type.ML_CEIL),
        r'\floor': KoreToken(r'\floor', KoreToken.Type.ML_FLOOR),
        r'\equals': KoreToken(r'\equals', KoreToken.Type.ML_EQUALS),
        r'\in': KoreToken(r'\in', KoreToken.Type.ML_IN),
        r'\next': KoreToken(r'\next', KoreToken.Type.ML_NEXT),
        r'\rewrites': KoreToken(r'\rewrites', KoreToken.Type.ML_REWRITES),
        r'\dv': KoreToken(r'\dv', KoreToken.Type.ML_DV),
        r'\left-assoc': KoreToken(r'\left-assoc', KoreToken.Type.ML_LEFT_ASSOC),
        r'\right-assoc': KoreToken(r'\right-assoc', KoreToken.Type.ML_RIGHT_ASSOC),
    }

    _KEYWORDS: Final = {
        'module': KoreToken('module', KoreToken.Type.KW_MODULE),
        'endmodule': KoreToken('endmodule', KoreToken.Type.KW_ENDMODULE),
        'import': KoreToken('import', KoreToken.Type.KW_IMPORT),
        'sort': KoreToken('sort', KoreToken.Type.KW_SORT),
        'hooked-sort': KoreToken('hooked-sort', KoreToken.Type.KW_HOOKED_SORT),
        'symbol': KoreToken('symbol', KoreToken.Type.KW_SYMBOL),
        'hooked-symbol': KoreToken('hooked-symbol', KoreToken.Type.KW_HOOKED_SYMBOL),
        'axiom': KoreToken('axiom', KoreToken.Type.KW_AXIOM),
        'claim': KoreToken('claim', KoreToken.Type.KW_CLAIM),
        'alias': KoreToken('alias', KoreToken.Type.KW_ALIAS),
        'where': KoreToken('where', KoreToken.Type.KW_WHERE),
    }

    _SIMPLE_CHARS: Final = {
        ',': KoreToken(',', KoreToken.Type.COMMA),
        '(': KoreToken('(', KoreToken.Type.LPAREN),
        ')': KoreToken(')', KoreToken.Type.RPAREN),
        '{': KoreToken('{', KoreToken.Type.LBRACE),
        '}': KoreToken('}', KoreToken.Type.RBRACE),
        '[': KoreToken('[', KoreToken.Type.LBRACK),
        ']': KoreToken(']', KoreToken.Type.RBRACK),
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
        actual = '<EOF>' if self._la is None else self._la

        if self._la != c:
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
            return KoreToken(':=', KoreToken.Type.WALRUS)

        return KoreToken(':', KoreToken.Type.COLON)

    def _string_token(self) -> KoreToken:
        buf: List[str] = []
        buf += self._match('"')
        while self._la != '"':
            if self._la == '\\':
                buf += self._consume()
            buf += self._consume()
        buf += self._consume()

        return KoreToken(''.join(buf), KoreToken.Type.STRING)

    def _symbol_id_or_ml_symbol_token(self) -> KoreToken:
        self._match('\\')
        name = self._id_text()
        symbol_id = f'\\{name}'

        if symbol_id in self._ML_SYMBOLS:
            return self._ML_SYMBOLS[symbol_id]

        return KoreToken(symbol_id, KoreToken.Type.SYMBOL_ID)

    def _set_var_id_token(self) -> KoreToken:
        self._match('@')
        name = self._id_text()
        return KoreToken(f'@{name}', KoreToken.Type.SET_VAR_ID)

    def _id_or_keyword_token(self) -> KoreToken:
        name = self._id_text()

        if name in self._KEYWORDS:
            return self._KEYWORDS[name]

        return KoreToken(name, KoreToken.Type.ID)

    def _id_text(self) -> str:
        buf: List[str] = []
        buf += self._match_any(self._ID_FIRST_CHARS)
        while self._la in self._ID_CHARS:
            buf += self._consume()
        return ''.join(buf)
