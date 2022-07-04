from abc import ABC
from dataclasses import dataclass
from enum import IntEnum
from itertools import chain
from typing import Final, Iterable, Iterator, List, Optional, Tuple, final

KEYWORDS: Final = {
    "module",
    "endmodule",
    "import",
    "sort",
    "hooked-sort",
    "symbol",
    "hooked-symbol",
    "axiom",
    "claim",
    "alias",
    "where",
}


_A_TO_Z_LC: Final = 'abcdefghijklmnopqrstuvwxyz'
_A_TO_Z_UC: Final = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
_0_TO_9: Final = '0123456789'

_ID_FST_CHR = set(_A_TO_Z_LC + _A_TO_Z_UC)
_ID_CHR = set(_0_TO_9 + "'-").union(_ID_FST_CHR)


def _has_id_syntax(s: str) -> bool:
    return len(s) > 0 and s[0] in _ID_FST_CHR and all(c in _ID_CHR for c in s[1:])


def is_id(s: str) -> bool:
    return _has_id_syntax(s) and s not in KEYWORDS


def is_symbol_id(s: str) -> bool:
    if len(s) < 1:
        return False

    if s[0] == '\\':
        return _has_id_syntax(s[1:])

    return is_id(s)


def is_set_var_id(s: str) -> bool:
    if len(s) < 1:
        return False

    if s[0] != '@':
        return False

    return _has_id_syntax(s[1:])


def check_id(s: str) -> None:
    if not is_id(s):
        raise ValueError(f'Expected identifier, found: {s}')


def check_symbol_id(s: str) -> None:
    if not is_symbol_id(s):
        raise ValueError(f'Expected symbol identifier, found: {s}')


def check_set_var_id(s: str) -> None:
    if not is_set_var_id(s):
        raise ValueError(f'Expected set variable identifier, found: {s}')


# TODO @overload


class Kore(ABC):
    ...


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
            token = f'\\x{hexa}'
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

        if not (32 <= ord(self._la) <= 122):
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
class StrLit(Kore):
    value: str

    def __init__(self, value: str):
        for _ in StrLitLexer(value):
            pass  # validate value

        object.__setattr__(self, 'value', value)

    def decode(self) -> str:
        return bytes(self.value, 'ascii').decode('unicode-escape')


class Sort(Kore, ABC):
    name: str


@final
@dataclass(frozen=True)
class SortVar(Sort):
    name: str

    def __init__(self, name: str):
        check_id(name)
        object.__setattr__(self, 'name', name)


@final
@dataclass(frozen=True)
class SortCons(Sort):
    name: str
    sorts: Tuple[Sort, ...]

    def __init__(self, name: str, sorts: Iterable[Sort] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sorts', tuple(sorts))


class Pattern(Kore, ABC):
    ...


class VarPattern(Pattern, ABC):
    name: str
    sort: Sort


@final
@dataclass(frozen=True)
class ElemVar(VarPattern):
    name: str
    sort: Sort

    def __init__(self, name: str, sort: Sort):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)


@final
@dataclass(frozen=True)
class SetVar(VarPattern):
    name: str
    sort: Sort

    def __init__(self, name: str, sort: Sort):
        check_set_var_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)


@final
@dataclass(frozen=True)
class Apply(Pattern):
    symbol: str
    sorts: Tuple[Sort, ...]
    patterns: Tuple[Pattern, ...]

    def __init__(self, symbol: str, sorts: Iterable[Sort], patterns: Iterable[Pattern]):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'patterns', tuple(patterns))


class MLPattern(Pattern, ABC):
    ...


class MLConn(MLPattern, ABC):
    sort: Sort


class NullaryConn(MLConn, ABC):
    ...


@final
@dataclass(frozen=True)
class Top(NullaryConn):
    sort: Sort


@final
@dataclass(frozen=True)
class Bottom(NullaryConn):
    sort: Sort


class UnaryConn(MLConn, ABC):
    pattern: Pattern


@final
@dataclass(frozen=True)
class Not(UnaryConn):
    sort: Sort
    pattern: Pattern


class BinaryConn(MLConn, ABC):
    left: Pattern
    right: Pattern

    def __iter__(self) -> Iterator[Pattern]:
        yield self.left
        yield self.right


@final
@dataclass(frozen=True)
class And(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class Or(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class Implies(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class Iff(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern


class MLQuant(MLPattern, ABC):
    sort: Sort
    var: ElemVar
    pattern: Pattern


@final
@dataclass(frozen=True)
class Exists(MLQuant):
    sort: Sort
    var: ElemVar
    pattern: Pattern


@final
@dataclass(frozen=True)
class Forall(MLQuant):
    sort: Sort
    var: ElemVar
    pattern: Pattern


class MLFixpoint(MLPattern, ABC):
    var: SetVar
    pattern: Pattern


@final
@dataclass(frozen=True)
class Mu(MLFixpoint):
    var: SetVar
    pattern: Pattern


@final
@dataclass(frozen=True)
class Nu(MLFixpoint):
    var: SetVar
    pattern: Pattern


class MLPred(MLPattern, ABC):
    ...


@final
@dataclass(frozen=True)
class Ceil(MLPred):
    op_sort: Sort
    sort: Sort
    pattern: Pattern


@final
@dataclass(frozen=True)
class Floor(MLPred):
    op_sort: Sort
    sort: Sort
    pattern: Pattern


@final
@dataclass(frozen=True)
class Equals(MLPred):
    left_sort: Sort
    right_sort: Sort
    left_pattern: Pattern
    right_pattern: Pattern


@final
@dataclass(frozen=True)
class In(MLPred):
    left_sort: Sort
    right_sort: Sort
    left_pattern: Pattern
    right_pattern: Pattern


class MLRewrite(MLPattern, ABC):
    sort: Sort


@final
@dataclass(frozen=True)
class Next(MLRewrite):
    sort: Sort
    pattern: Pattern


@final
@dataclass(frozen=True)
class Rewrites(MLRewrite):
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class DomVal(MLPattern):
    sort: Sort
    value: StrLit


# TODO
class MLSyntaxSugar(MLPattern, ABC):
    ...


@final
@dataclass(frozen=True)
class Attr(Kore):
    symbol: str
    params: Tuple[StrLit, ...]

    def __init__(self, symbol: str, params: Iterable[StrLit]):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'params', tuple(params))


class WithAttrs(ABC):
    attrs: Tuple[Attr, ...]


class Sentence(Kore, WithAttrs, ABC):
    ...


@final
@dataclass(frozen=True)
class Import(Sentence):
    module_name: str
    attrs: Tuple[Attr, ...]

    def __init__(self, module_name: str, attrs: Iterable[Attr] = ()):
        check_id(module_name)
        object.__setattr__(self, 'module_name', module_name)
        object.__setattr__(self, 'attrs', tuple(attrs))


@final
@dataclass(frozen=True)
class SortDecl(Sentence):
    name: str
    vars: Tuple[SortVar, ...]
    hooked: bool
    attrs: Tuple[Attr, ...]

    def __init__(self, name: str, vars: Iterable[SortVar], hooked=False, attrs: Iterable[Attr] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'hooked', hooked)
        object.__setattr__(self, 'attrs', tuple(attrs))


@final
@dataclass(frozen=True)
class Symbol(Kore):
    name: str
    vars: Tuple[SortVar, ...]

    def __init__(self, name: str, vars: Iterable[SortVar]):
        check_symbol_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))


@final
@dataclass(frozen=True)
class SymbolDecl(Sentence):
    symbol: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    hooked: bool
    attrs: Tuple[Attr, ...]

    def __init__(self, symbol: Symbol, sort_params: Iterable[Sort], sort: Sort, hooked=False, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'hooked', hooked)
        object.__setattr__(self, 'attrs', tuple(attrs))


@final
@dataclass(frozen=True)
class AliasDecl(Sentence):
    alias: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    left: Apply
    right: Pattern
    hooked: bool
    attrs: Tuple[Attr, ...]

    def __init__(
        self,
        alias: Symbol,
        sort_params: Iterable[Sort],
        sort: Sort,
        left: Apply,
        right: Pattern,
        hooked=False,
        attrs: Iterable[Attr] = ()
    ):
        object.__setattr__(self, 'alias', alias)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
        object.__setattr__(self, 'hooked', hooked)
        object.__setattr__(self, 'attrs', tuple(attrs))


class AxiomLike(Sentence, ABC):
    vars: Tuple[SortVar, ...]
    pattern: Pattern


@final
@dataclass(frozen=True)
class Axiom(AxiomLike):
    vars: Tuple[SortVar, ...]
    pattern: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))


@final
@dataclass(frozen=True)
class Claim(AxiomLike):
    vars: Tuple[SortVar, ...]
    pattern: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))


@final
@dataclass(frozen=True)
class Module(Kore, WithAttrs):
    name: str
    sentences: Tuple[Sentence, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, name: str, sentences: Iterable[Sentence] = (), attrs: Iterable[Attr] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'attrs', tuple(attrs))


@final
@dataclass(frozen=True)
class Definition(Kore, WithAttrs):
    modules: Tuple[Module, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, modules: Iterable[Module] = (), attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'attrs', tuple(attrs))
