from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import IntEnum
from itertools import chain
from typing import (
    ClassVar,
    Final,
    Iterable,
    Iterator,
    List,
    Optional,
    Tuple,
    Union,
    final,
)

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


def _bracketed(elems: Iterable[str], lbrac: str, rbrac: str) -> str:
    elems = tuple(elems)
    return lbrac + ' ' + ', '.join(elems) + (' ' if elems else '') + rbrac


def _braced(elems: Iterable[str]) -> str:
    return _bracketed(elems, '{', '}')


def _brackd(elems: Iterable[str]) -> str:
    return _bracketed(elems, '[', ']')


def _parend(elems: Iterable[str]) -> str:
    return _bracketed(elems, '(', ')')


# TODO @overload


class Kore(ABC):
    ...

    @property
    @abstractmethod
    def text(self) -> str:
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


class Sort(Kore, ABC):
    name: str


@final
@dataclass(frozen=True)
class SortVar(Sort):
    name: str

    def __init__(self, name: str):
        check_id(name)
        object.__setattr__(self, 'name', name)

    @property
    def text(self) -> str:
        return self.name


@final
@dataclass(frozen=True)
class SortCons(Sort):
    name: str
    sorts: Tuple[Sort, ...]

    def __init__(self, name: str, sorts: Iterable[Sort] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sorts', tuple(sorts))

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(sort.text for sort in self.sorts)


class Pattern(Kore, ABC):
    ...


class VarPattern(Pattern, ABC):
    name: str
    sort: Sort

    @property
    def text(self) -> str:
        return f'{self.name} : {self.sort.text}'


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
class StrLit(Pattern):
    value: str

    def __init__(self, value: str):
        for _ in StrLitLexer(value):
            pass  # validate value

        object.__setattr__(self, 'value', value)

    @property
    def text(self) -> str:
        return f'"{self.value}"'

    @property
    def decoded(self) -> str:
        return bytes(self.value, 'ascii').decode('unicode-escape')


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

    @property
    def text(self) -> str:
        return self.symbol + ' ' + _braced(sort.text for sort in self.sorts) + ' ' + _parend(pattern.text for pattern in self.patterns)


class MLPattern(Pattern, ABC):
    symbol: ClassVar[str]


class MLConn(MLPattern, ABC):
    sort: Sort

    @property
    @abstractmethod
    def patterns(self) -> Tuple[Pattern, ...]:
        ...

    @property
    def text(self) -> str:
        return self.symbol + ' { ' + self.sort.text + ' } ' + _parend(pattern.text for pattern in self.patterns)


class NullaryConn(MLConn, ABC):

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return ()


@final
@dataclass(frozen=True)
class Top(NullaryConn):
    symbol = '\\top'
    sort: Sort


@final
@dataclass(frozen=True)
class Bottom(NullaryConn):
    symbol = '\\bottom'
    sort: Sort


class UnaryConn(MLConn, ABC):
    pattern: Pattern

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return (self.pattern,)


@final
@dataclass(frozen=True)
class Not(UnaryConn):
    symbol = '\\not'
    sort: Sort
    pattern: Pattern


class BinaryConn(MLConn, ABC):
    left: Pattern
    right: Pattern

    def __iter__(self) -> Iterator[Pattern]:
        yield self.left
        yield self.right

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return (self.left, self.right)


@final
@dataclass(frozen=True)
class And(BinaryConn):
    symbol = '\\and'
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class Or(BinaryConn):
    symbol = '\\or'
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class Implies(BinaryConn):
    symbol = '\\implies'
    sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class Iff(BinaryConn):
    symbol = '\\iff'
    sort: Sort
    left: Pattern
    right: Pattern


class MLQuant(MLPattern, ABC):
    sort: Sort
    var: ElemVar
    pattern: Pattern

    @property
    def text(self) -> str:
        return self.symbol + ' { ' + self.sort.text + ' } ' + _parend((self.var.text, self.pattern.text))


@final
@dataclass(frozen=True)
class Exists(MLQuant):
    symbol = '\\exists'
    sort: Sort
    var: ElemVar
    pattern: Pattern


@final
@dataclass(frozen=True)
class Forall(MLQuant):
    symbol = '\\forall'
    sort: Sort
    var: ElemVar
    pattern: Pattern


class MLFixpoint(MLPattern, ABC):
    var: SetVar
    pattern: Pattern

    @property
    def text(self) -> str:
        return self.symbol + ' { } ' + _parend((self.var.text, self.pattern.text))


@final
@dataclass(frozen=True)
class Mu(MLFixpoint):
    symbol = '\\mu'
    var: SetVar
    pattern: Pattern


@final
@dataclass(frozen=True)
class Nu(MLFixpoint):
    symbol = '\\nu'
    var: SetVar
    pattern: Pattern


class MLPred(MLPattern, ABC):
    ...


class RoundPred(MLPred, ABC):
    op_sort: Sort
    sort: Sort
    pattern: Pattern

    @property
    def text(self) -> str:
        return self.symbol + ' ' + _braced((self.op_sort.text, self.sort.text)) + ' ( ' + self.pattern.text + ' )'


@final
@dataclass(frozen=True)
class Ceil(RoundPred):
    symbol = '\\ceil'
    op_sort: Sort
    sort: Sort
    pattern: Pattern


@final
@dataclass(frozen=True)
class Floor(RoundPred):
    symbol = '\\floor'
    op_sort: Sort
    sort: Sort
    pattern: Pattern


class BinaryPred(MLPred, ABC):
    left_sort: Sort
    right_sort: Sort
    left: Pattern
    right: Pattern

    @property
    def text(self) -> str:
        return ' '.join([
            self.symbol,
            _braced((self.left_sort.text, self.right_sort.text)),
            _parend((self.left.text, self.right.text)),
        ])


@final
@dataclass(frozen=True)
class Equals(BinaryPred):
    symbol = '\\equals'
    left_sort: Sort
    right_sort: Sort
    left: Pattern
    right: Pattern


@final
@dataclass(frozen=True)
class In(BinaryPred):
    symbol = '\\in'
    left_sort: Sort
    right_sort: Sort
    left: Pattern
    right: Pattern


class MLRewrite(MLPattern, ABC):
    sort: Sort


@final
@dataclass(frozen=True)
class Next(MLRewrite):
    symbol = '\\next'
    sort: Sort
    pattern: Pattern

    @property
    def text(self) -> str:
        return self.symbol + ' { ' + self.sort.text + ' } ( ' + self.pattern.text + ' )'


@final
@dataclass(frozen=True)
class Rewrites(MLRewrite):
    symbol = '\\rewrites'
    sort: Sort
    left: Pattern
    right: Pattern

    @property
    def text(self) -> str:
        return self.symbol + ' { ' + self.sort.text + ' } ' + _parend((self.left.text, self.right.text))


@final
@dataclass(frozen=True)
class DomVal(MLPattern):
    symbol = '\\dv'
    sort: Sort
    value: StrLit

    @property
    def text(self) -> str:
        return self.symbol + ' { ' + self.sort.text + ' } ( ' + self.value.text + ' )'


# TODO
class MLSyntaxSugar(MLPattern, ABC):
    ...


@final
@dataclass(frozen=True)
class Attr(Kore):
    symbol: str
    params: Tuple[Union[StrLit, 'Attr'], ...]

    def __init__(self, symbol: str, params: Iterable[Union[StrLit, 'Attr']] = ()):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'params', tuple(params))

    @property
    def text(self) -> str:
        return self.symbol + ' { } ' + _parend(param.text for param in self.params)


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

    @property
    def text(self) -> str:
        return ' '.join([
            'import',
            self.module_name,
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class SortDecl(Sentence):
    name: str
    vars: Tuple[SortVar, ...]
    attrs: Tuple[Attr, ...]
    hooked: bool

    def __init__(self, name: str, vars: Iterable[SortVar], attrs: Iterable[Attr] = (), *, hooked=False):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    @property
    def text(self) -> str:
        return ' '.join([
            'hooked-sort' if self.hooked else 'sort',
            self.name,
            _braced(var.text for var in self.vars),
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class Symbol(Kore):
    name: str
    vars: Tuple[SortVar, ...]

    def __init__(self, name: str, vars: Iterable[SortVar] = ()):
        check_symbol_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(var.text for var in self.vars)


@final
@dataclass(frozen=True)
class SymbolDecl(Sentence):
    symbol: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    attrs: Tuple[Attr, ...]
    hooked: bool

    def __init__(self, symbol: Symbol, sort_params: Iterable[Sort], sort: Sort, attrs: Iterable[Attr] = (), *, hooked=False):
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    @property
    def text(self) -> str:
        return ' '.join([
            'hooked-symbol' if self.hooked else 'symbol',
            self.symbol.text,
            _parend(sort.text for sort in self.sort_params),
            ':',
            self.sort.text,
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class AliasDecl(Sentence):
    alias: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    left: Apply
    right: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(
        self,
        alias: Symbol,
        sort_params: Iterable[Sort],
        sort: Sort,
        left: Apply,
        right: Pattern,
        attrs: Iterable[Attr] = (),
    ):
        object.__setattr__(self, 'alias', alias)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
        object.__setattr__(self, 'attrs', tuple(attrs))

    @property
    def text(self) -> str:
        return ' '.join([
            'alias',
            self.alias.text,
            _parend(sort.text for sort in self.sort_params),
            ':',
            self.sort.text,
            'where',
            self.left.text,
            ':=',
            self.right.text,
            _brackd(attr.text for attr in self.attrs),
        ])


class AxiomLike(Sentence, ABC):
    label: ClassVar[str]
    vars: Tuple[SortVar, ...]
    pattern: Pattern

    @property
    def text(self) -> str:
        return ' '.join([
            self.label,
            _braced(var.text for var in self.vars),
            self.pattern.text,
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class Axiom(AxiomLike):
    label = 'axiom'
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
    label = 'claim'
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

    @property
    def text(self) -> str:
        return '\n'.join(
            [f'module {self.name}'] +                                   # noqa: W504
            [f'    {sentence.text}' for sentence in self.sentences] +   # noqa: W504
            ['endmodule ' + _brackd(attr.text for attr in self.attrs)]  # noqa: W504
        )


@final
@dataclass(frozen=True)
class Definition(Kore, WithAttrs):
    modules: Tuple[Module, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, modules: Iterable[Module] = (), attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'attrs', tuple(attrs))

    @property
    def text(self) -> str:
        return '\n\n'.join([
            _brackd(attr.text for attr in self.attrs),
        ] + [module.text for module in self.modules])
