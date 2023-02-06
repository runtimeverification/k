import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property
from typing import (
    Any,
    Callable,
    ClassVar,
    Dict,
    Final,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Tuple,
    Type,
    TypeVar,
    Union,
    final,
)

from ..utils import check_type
from .lexer import KoreLexer, KoreStringLexer


def check_id(s: str) -> None:
    lexer = KoreLexer(s)
    try:
        lexer.id()
        lexer.eof()
    except ValueError as err:
        raise ValueError(f'Expected identifier, found: {s}') from err


def check_symbol_id(s: str) -> None:
    lexer = KoreLexer(s)
    try:
        lexer.symbol_id()
        lexer.eof()
    except ValueError as err:
        raise ValueError(f'Expected symbol identifier, found: {s}') from err


def check_set_var_id(s: str) -> None:
    lexer = KoreLexer(s)
    try:
        lexer.set_var_id()
        lexer.eof()
    except ValueError as err:
        raise ValueError(f'Expected set variable identifier, found: {s}') from err


def encode_kore_str(s: str) -> str:
    res: List[str] = []
    for c in s:
        if ord(c) == 12:
            res += '\\f'
        elif ord(c) == 34:
            res += '\\"'
        else:
            res += c.encode('unicode-escape').decode('ascii')
    return ''.join(res)


def decode_kore_str(s: str) -> str:
    res: List[str] = []
    for token, _ in KoreStringLexer(s):
        if token == '\\f':
            res += '\f'
        elif token == '\\"':
            res += '"'
        else:
            res += token.encode('ascii').decode('unicode-escape')
    return ''.join(res)


def _bracketed(elems: Iterable[str], lbrac: str, rbrac: str) -> str:
    elems = tuple(elems)
    return lbrac + ' ' + ', '.join(elems) + (' ' if elems else '') + rbrac


def _braced(elems: Iterable[str]) -> str:
    return _bracketed(elems, '{', '}')


def _brackd(elems: Iterable[str]) -> str:
    return _bracketed(elems, '[', ']')


def _parend(elems: Iterable[str]) -> str:
    return _bracketed(elems, '(', ')')


# TODO Constructor @overloads


T = TypeVar('T', bound='Kore')
P = TypeVar('P', bound='Pattern')
WS = TypeVar('WS', bound='WithSort')
WA = TypeVar('WA', bound='WithAttrs')
ML = TypeVar('ML', bound='MLPattern')


def unsupported() -> Any:
    raise RuntimeError('Unsupported operation')


class Kore(ABC):
    _TAGS: Final = {
        'SortVar',
        'SortApp',
        'String',
        'EVar',
        'SVar',
        'App',
        'Top',
        'Bottom',
        'Not',
        'And',
        'Or',
        'Implies',
        'Iff',
        'Exists',
        'Forall',
        'Mu',
        'Nu',
        'Ceil',
        'Floor',
        'Equals',
        'In',
        'Next',
        'Rewrites',
        'DV',
        'LeftAssoc',
        'RightAssoc',
    }

    @classmethod
    @abstractmethod
    def _tag(cls) -> str:  # TODO This should be an abstract immutable class attribute for efficiency
        ...

    @classmethod
    def from_dict(cls: Type[T], dct: Mapping[str, Any]) -> T:
        tag = Kore._get_tag(dct)

        if tag not in Kore._TAGS:
            raise ValueError(f'Invalid Kore tag: {tag}')

        actual_cls = globals()[tag]

        if not issubclass(actual_cls, cls):
            raise ValueError(f'Expected {cls.__name__} tag, found: {tag}')

        return actual_cls.from_dict(dct)

    @classmethod
    def from_json(cls: Type[T], s: str) -> T:
        return cls.from_dict(json.loads(s))

    @staticmethod
    def _get_tag(dct: Mapping[str, Any]) -> str:
        if 'tag' not in dct:
            raise ValueError("Attribute 'tag' is missing")
        return dct['tag']

    @classmethod
    def _check_tag(cls: Type[T], dct: Mapping[str, Any]) -> None:
        tag = cls._get_tag(dct)
        if tag != cls._tag():
            raise ValueError(f'Expected "tag" value: {cls._tag()}, got: {tag}')

    @property
    def json(self) -> str:
        return json.dumps(self.dict, sort_keys=True)

    @property
    @abstractmethod
    def dict(self) -> Dict[str, Any]:
        ...

    @property
    @abstractmethod
    def text(self) -> str:
        ...


class Sort(Kore):
    name: str


class WithSort(ABC):
    sort: Sort

    @abstractmethod
    def let_sort(self: WS, sort: Sort) -> WS:
        ...

    def map_sort(self: WS, f: Callable[[Sort], Sort]) -> WS:
        return self.let_sort(f(self.sort))


@final
@dataclass(frozen=True)
class SortVar(Sort):
    name: str

    def __init__(self, name: str):
        check_id(name)
        object.__setattr__(self, 'name', name)

    def let(self, *, name: Optional[str] = None) -> 'SortVar':
        name = name if name is not None else self.name
        return SortVar(name=name)

    @classmethod
    def _tag(cls) -> str:
        return 'SortVar'

    @classmethod
    def from_dict(cls: Type['SortVar'], dct: Mapping[str, Any]) -> 'SortVar':
        cls._check_tag(dct)
        return SortVar(name=dct['name'])

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'name': self.name}

    @property
    def text(self) -> str:
        return self.name


@final
@dataclass(frozen=True)
class SortApp(Sort):
    name: str
    sorts: Tuple[Sort, ...]

    def __init__(self, name: str, sorts: Iterable[Sort] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sorts', tuple(sorts))

    def let(self, *, name: Optional[str] = None, sorts: Optional[Iterable[Sort]] = None) -> 'SortApp':
        name = name if name is not None else self.name
        sorts = sorts if sorts is not None else self.sorts
        return SortApp(name=name, sorts=sorts)

    @classmethod
    def _tag(cls) -> str:
        return 'SortApp'

    @classmethod
    def from_dict(cls: Type['SortApp'], dct: Mapping[str, Any]) -> 'SortApp':
        cls._check_tag(dct)
        return SortApp(name=dct['name'], sorts=(Sort.from_dict(arg) for arg in dct['args']))

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'name': self.name, 'args': [sort.dict for sort in self.sorts]}

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(sort.text for sort in self.sorts)


class Pattern(Kore):
    @property
    @abstractmethod
    def patterns(self) -> Tuple['Pattern', ...]:
        ...

    @abstractmethod
    def let_patterns(self: P, patterns: Iterable['Pattern']) -> P:
        ...

    def map_patterns(self: P, f: Callable[['Pattern'], 'Pattern']) -> P:
        return self.let_patterns(patterns=(f(pattern) for pattern in self.patterns))

    def bottom_up(self, f: Callable[['Pattern'], 'Pattern']) -> 'Pattern':
        return f(self.map_patterns(lambda pattern: pattern.bottom_up(f)))

    def top_down(self, f: Callable[['Pattern'], 'Pattern']) -> 'Pattern':
        return f(self).map_patterns(lambda pattern: pattern.top_down(f))


class VarPattern(Pattern, WithSort):
    name: str
    sort: Sort

    @property
    def patterns(self) -> Tuple[()]:
        return ()

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'name': self.name, 'sort': self.sort.dict}

    @property
    def text(self) -> str:
        return f'{self.name} : {self.sort.text}'


@final
@dataclass(frozen=True)
class EVar(VarPattern):
    name: str
    sort: Sort

    def __init__(self, name: str, sort: Sort):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)

    def let(self, *, name: Optional[str] = None, sort: Optional[Sort] = None) -> 'EVar':
        name = name if name is not None else self.name
        sort = sort if sort is not None else self.sort
        return EVar(name=name, sort=sort)

    def let_sort(self, sort: Sort) -> 'EVar':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'EVar':
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'EVar'

    @classmethod
    def from_dict(cls: Type['EVar'], dct: Mapping[str, Any]) -> 'EVar':
        cls._check_tag(dct)
        return EVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class SVar(VarPattern):
    name: str
    sort: Sort

    def __init__(self, name: str, sort: Sort):
        check_set_var_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)

    def let(self, *, name: Optional[str] = None, sort: Optional[Sort] = None) -> 'SVar':
        name = name if name is not None else self.name
        sort = sort if sort is not None else self.sort
        return SVar(name=name, sort=sort)

    def let_sort(self, sort: Sort) -> 'SVar':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'SVar':
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'SVar'

    @classmethod
    def from_dict(cls: Type['SVar'], dct: Mapping[str, Any]) -> 'SVar':
        cls._check_tag(dct)
        return SVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class String(Pattern):
    value: str

    def let(self, *, value: Optional[str] = None) -> 'String':
        value = value if value is not None else self.value
        return String(value=value)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'String':
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'String'

    @classmethod
    def from_dict(cls: Type['String'], dct: Mapping[str, Any]) -> 'String':
        cls._check_tag(dct)
        return String(value=dct['value'])

    @property
    def patterns(self) -> Tuple[()]:
        return ()

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'value': self.value}

    @property
    def text(self) -> str:
        return '"' + encode_kore_str(self.value) + '"'


@final
@dataclass(frozen=True)
class App(Pattern):
    symbol: str
    sorts: Tuple[Sort, ...]
    args: Tuple[Pattern, ...]

    def __init__(self, symbol: str, sorts: Iterable[Sort] = (), args: Iterable[Pattern] = ()):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'args', tuple(args))

    def let(
        self,
        *,
        symbol: Optional[str] = None,
        sorts: Optional[Iterable] = None,
        args: Optional[Iterable] = None,
    ) -> 'App':
        symbol = symbol if symbol is not None else self.symbol
        sorts = sorts if sorts is not None else self.sorts
        args = args if args is not None else self.args
        return App(symbol=symbol, sorts=sorts, args=args)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'App':
        return self.let(args=patterns)

    @classmethod
    def _tag(cls) -> str:
        return 'App'

    @classmethod
    def from_dict(cls: Type['App'], dct: Mapping[str, Any]) -> 'App':
        cls._check_tag(dct)
        return App(
            symbol=dct['name'],
            sorts=(Sort.from_dict(sort) for sort in dct['sorts']),
            args=(Pattern.from_dict(arg) for arg in dct['args']),
        )

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return self.args

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'name': self.symbol,
            'sorts': [sort.dict for sort in self.sorts],
            'args': [pattern.dict for pattern in self.args],
        }

    @property
    def text(self) -> str:
        return (
            self.symbol
            + ' '
            + _braced(sort.text for sort in self.sorts)
            + ' '
            + _parend(args.text for args in self.args)
        )


class MLPattern(Pattern):
    @classmethod
    @abstractmethod
    def symbol(cls) -> str:
        ...

    @classmethod
    def of(cls: Type[ML], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> ML:
        actual_cls = ML_SYMBOLS.get(symbol)

        if not actual_cls:
            raise ValueError(f'Invalid MLPattern symbol: {symbol}')

        if not issubclass(actual_cls, cls):
            raise ValueError(f'Expected {cls.__name__} symbol, found: {symbol}')

        return actual_cls.of(symbol, sorts, patterns)

    @classmethod
    def _check_symbol(cls: Type[ML], symbol: str) -> None:
        if symbol != cls.symbol():
            raise ValueError(f'Expected "symbol" value: {cls.symbol()}, got: {symbol}')

    @property
    @abstractmethod
    def sorts(self) -> Tuple[Sort, ...]:
        ...

    @property
    def ctor_patterns(self) -> Tuple[Pattern, ...]:
        """
        Patterns used to construct the term with `of`.
        Except for `Assoc`, `DV`, `MLFixpoint` and `MLQuant` it coincides with `patterns`.
        """
        return self.patterns

    @property
    def text(self) -> str:
        return (
            self.symbol()
            + ' '
            + _braced(sort.text for sort in self.sorts)
            + ' '
            + _parend(pattern.text for pattern in self.ctor_patterns)
        )


class MLConn(MLPattern, WithSort):
    @property
    def sorts(self) -> Tuple[Sort]:
        return (self.sort,)


class NullaryConn(MLConn):
    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'sort': self.sort.dict}

    @property
    def patterns(self) -> Tuple[()]:
        return ()


@final
@dataclass(frozen=True)
class Top(NullaryConn):
    sort: Sort

    def let(self, *, sort: Optional[Sort] = None) -> 'Top':
        sort = sort if sort is not None else self.sort
        return Top(sort=sort)

    def let_sort(self: 'Top', sort: Sort) -> 'Top':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Top':
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'Top'

    @classmethod
    def symbol(cls) -> str:
        return '\\top'

    @classmethod
    def of(cls: Type['Top'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Top':
        cls._check_symbol(symbol)
        (sort,) = sorts
        () = patterns
        return Top(sort=sort)

    @classmethod
    def from_dict(cls: Type['Top'], dct: Mapping[str, Any]) -> 'Top':
        cls._check_tag(dct)
        return Top(sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class Bottom(NullaryConn):
    sort: Sort

    def let(self, *, sort: Optional[Sort] = None) -> 'Bottom':
        sort = sort if sort is not None else self.sort
        return Bottom(sort=sort)

    def let_sort(self: 'Bottom', sort: Sort) -> 'Bottom':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Bottom':
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'Bottom'

    @classmethod
    def symbol(cls) -> str:
        return '\\bottom'

    @classmethod
    def of(cls: Type['Bottom'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Bottom':
        cls._check_symbol(symbol)
        (sort,) = sorts
        () = patterns
        return Bottom(sort=sort)

    @classmethod
    def from_dict(cls: Type['Bottom'], dct: Mapping[str, Any]) -> 'Bottom':
        cls._check_tag(dct)
        return Bottom(sort=Sort.from_dict(dct['sort']))


class UnaryConn(MLConn):
    pattern: Pattern

    @property
    def patterns(self) -> Tuple[Pattern]:
        return (self.pattern,)

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'sort': self.sort.dict, 'arg': self.pattern.dict}


@final
@dataclass(frozen=True)
class Not(UnaryConn):
    sort: Sort
    pattern: Pattern

    def let(self, *, sort: Optional[Sort] = None, pattern: Optional[Pattern] = None) -> 'Not':
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Not(sort=sort, pattern=pattern)

    def let_sort(self: 'Not', sort: Sort) -> 'Not':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Not':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Not'

    @classmethod
    def symbol(cls) -> str:
        return '\\not'

    @classmethod
    def of(cls: Type['Not'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Not':
        cls._check_symbol(symbol)
        (sort,) = sorts
        (pattern,) = patterns
        return Not(sort=sort, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Not'], dct: Mapping[str, Any]) -> 'Not':
        cls._check_tag(dct)
        return Not(sort=Sort.from_dict(dct['sort']), pattern=Pattern.from_dict(dct['arg']))


class BinaryConn(MLConn):
    left: Pattern
    right: Pattern

    def __iter__(self) -> Iterator[Pattern]:
        yield self.left
        yield self.right

    @property
    def patterns(self) -> Tuple[Pattern, Pattern]:
        return (self.left, self.right)

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'sort': self.sort.dict,
            'first': self.left.dict,
            'second': self.right.dict,
        }


@final
@dataclass(frozen=True)
class And(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'And':
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return And(sort=sort, left=left, right=right)

    def let_sort(self: 'And', sort: Sort) -> 'And':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'And':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'And'

    @classmethod
    def symbol(cls) -> str:
        return '\\and'

    @classmethod
    def of(cls: Type['And'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'And':
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return And(sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['And'], dct: Mapping[str, Any]) -> 'And':
        cls._check_tag(dct)
        return And(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


@final
@dataclass(frozen=True)
class Or(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'Or':
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Or(sort=sort, left=left, right=right)

    def let_sort(self: 'Or', sort: Sort) -> 'Or':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Or':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Or'

    @classmethod
    def symbol(cls) -> str:
        return '\\or'

    @classmethod
    def of(cls: Type['Or'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Or':
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Or(sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['Or'], dct: Mapping[str, Any]) -> 'Or':
        cls._check_tag(dct)
        return Or(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


@final
@dataclass(frozen=True)
class Implies(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'Implies':
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Implies(sort=sort, left=left, right=right)

    def let_sort(self: 'Implies', sort: Sort) -> 'Implies':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Implies':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Implies'

    @classmethod
    def symbol(cls) -> str:
        return '\\implies'

    @classmethod
    def of(
        cls: Type['Implies'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()
    ) -> 'Implies':
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Implies(sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['Implies'], dct: Mapping[str, Any]) -> 'Implies':
        cls._check_tag(dct)
        return Implies(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


@final
@dataclass(frozen=True)
class Iff(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'Iff':
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Iff(sort=sort, left=left, right=right)

    def let_sort(self: 'Iff', sort: Sort) -> 'Iff':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Iff':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Iff'

    @classmethod
    def symbol(cls) -> str:
        return '\\iff'

    @classmethod
    def of(cls: Type['Iff'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Iff':
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Iff(sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['Iff'], dct: Mapping[str, Any]) -> 'Iff':
        cls._check_tag(dct)
        return Iff(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


class MLQuant(MLPattern, WithSort):
    sort: Sort
    var: EVar  # TODO Should this be inlined to var_name, var_sort?
    pattern: Pattern

    @property
    def sorts(self) -> Tuple[Sort]:
        return (self.sort,)

    @property
    def patterns(self) -> Tuple[Pattern]:
        return (self.pattern,)

    @property
    def ctor_patterns(self) -> Tuple[EVar, Pattern]:
        return (self.var, self.pattern)

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'sort': self.sort.dict,
            'var': self.var.name,
            'varSort': self.var.sort.dict,
            'arg': self.pattern.dict,
        }


@final
@dataclass(frozen=True)
class Exists(MLQuant):
    sort: Sort
    var: EVar
    pattern: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        var: Optional[EVar] = None,
        pattern: Optional[Pattern] = None,
    ) -> 'Exists':
        sort = sort if sort is not None else self.sort
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Exists(sort=sort, var=var, pattern=pattern)

    def let_sort(self, sort: Sort) -> 'Exists':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Exists':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Exists'

    @classmethod
    def symbol(cls) -> str:
        return '\\exists'

    @classmethod
    def of(cls: Type['Exists'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Exists':
        cls._check_symbol(symbol)
        (sort,) = sorts
        var, pattern = patterns
        var = check_type(var, EVar)
        return Exists(sort=sort, var=var, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Exists'], dct: Mapping[str, Any]) -> 'Exists':
        cls._check_tag(dct)
        return Exists(
            sort=Sort.from_dict(dct['sort']),
            var=EVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=Pattern.from_dict(dct['arg']),
        )


@final
@dataclass(frozen=True)
class Forall(MLQuant):
    sort: Sort
    var: EVar
    pattern: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        var: Optional[EVar] = None,
        pattern: Optional[Pattern] = None,
    ) -> 'Forall':
        sort = sort if sort is not None else self.sort
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Forall(sort=sort, var=var, pattern=pattern)

    def let_sort(self, sort: Sort) -> 'Forall':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Forall':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Forall'

    @classmethod
    def symbol(cls) -> str:
        return '\\forall'

    @classmethod
    def of(cls: Type['Forall'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Forall':
        cls._check_symbol(symbol)
        (sort,) = sorts
        var, pattern = patterns
        var = check_type(var, EVar)
        return Forall(sort=sort, var=var, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Forall'], dct: Mapping[str, Any]) -> 'Forall':
        cls._check_tag(dct)
        return Forall(
            sort=Sort.from_dict(dct['sort']),
            var=EVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=Pattern.from_dict(dct['arg']),
        )


class MLFixpoint(MLPattern):
    var: SVar  # TODO Should this be inlined to var_name, var_sort?
    pattern: Pattern

    @property
    def sorts(self) -> Tuple[()]:
        return ()

    @property
    def patterns(self) -> Tuple[Pattern]:
        return (self.pattern,)

    @property
    def ctor_patterns(self) -> Tuple[SVar, Pattern]:
        return (self.var, self.pattern)

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'var': self.var.name,
            'varSort': self.var.sort.dict,
            'arg': self.pattern.dict,
        }


@final
@dataclass(frozen=True)
class Mu(MLFixpoint):
    var: SVar
    pattern: Pattern

    def let(self, *, var: Optional[SVar] = None, pattern: Optional[Pattern] = None) -> 'Mu':
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Mu(var=var, pattern=pattern)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Mu':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Mu'

    @classmethod
    def symbol(cls) -> str:
        return '\\mu'

    @classmethod
    def of(cls: Type['Mu'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Mu':
        cls._check_symbol(symbol)
        () = sorts
        var, pattern = patterns
        var = check_type(var, SVar)
        return Mu(var=var, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Mu'], dct: Mapping[str, Any]) -> 'Mu':
        cls._check_tag(dct)
        return Mu(
            var=SVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=Pattern.from_dict(dct['arg']),
        )


@final
@dataclass(frozen=True)
class Nu(MLFixpoint):
    var: SVar
    pattern: Pattern

    def let(self, *, var: Optional[SVar] = None, pattern: Optional[Pattern] = None) -> 'Nu':
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Nu(var=var, pattern=pattern)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Nu':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Nu'

    @classmethod
    def symbol(cls) -> str:
        return '\\nu'

    @classmethod
    def of(cls: Type['Nu'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Nu':
        cls._check_symbol(symbol)
        () = sorts
        var, pattern = patterns
        var = check_type(var, SVar)
        return Nu(var=var, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Nu'], dct: Mapping[str, Any]) -> 'Nu':
        cls._check_tag(dct)
        return Nu(
            var=SVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=Pattern.from_dict(dct['arg']),
        )


class MLPred(MLPattern, WithSort):
    op_sort: Sort


class RoundPred(MLPred):
    pattern: Pattern

    @property
    def sorts(self) -> Tuple[Sort, Sort]:
        return (self.op_sort, self.sort)

    @property
    def patterns(self) -> Tuple[Pattern]:
        return (self.pattern,)

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'argSort': self.op_sort.dict,
            'sort': self.sort.dict,
            'arg': self.pattern.dict,
        }


@final
@dataclass(frozen=True)
class Ceil(RoundPred):
    op_sort: Sort
    sort: Sort
    pattern: Pattern

    def let(
        self,
        *,
        op_sort: Optional[Sort] = None,
        sort: Optional[Sort] = None,
        pattern: Optional[Pattern] = None,
    ) -> 'Ceil':
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Ceil(op_sort=op_sort, sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> 'Ceil':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Ceil':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Ceil'

    @classmethod
    def symbol(cls) -> str:
        return '\\ceil'

    @classmethod
    def of(cls: Type['Ceil'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Ceil':
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        (pattern,) = patterns
        return Ceil(op_sort=op_sort, sort=sort, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Ceil'], dct: Mapping[str, Any]) -> 'Ceil':
        cls._check_tag(dct)
        return Ceil(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            pattern=Pattern.from_dict(dct['arg']),
        )


@final
@dataclass(frozen=True)
class Floor(RoundPred):
    op_sort: Sort
    sort: Sort
    pattern: Pattern

    def let(
        self,
        *,
        op_sort: Optional[Sort] = None,
        sort: Optional[Sort] = None,
        pattern: Optional[Pattern] = None,
    ) -> 'Floor':
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Floor(op_sort=op_sort, sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> 'Floor':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Floor':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Floor'

    @classmethod
    def symbol(cls) -> str:
        return '\\floor'

    @classmethod
    def of(cls: Type['Floor'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Floor':
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        (pattern,) = patterns
        return Floor(op_sort=op_sort, sort=sort, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Floor'], dct: Mapping[str, Any]) -> 'Floor':
        cls._check_tag(dct)
        return Floor(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            pattern=Pattern.from_dict(dct['arg']),
        )


class BinaryPred(MLPred):
    left: Pattern
    right: Pattern

    @property
    def sorts(self) -> Tuple[Sort, Sort]:
        return (self.op_sort, self.sort)

    @property
    def patterns(self) -> Tuple[Pattern, Pattern]:
        return (self.left, self.right)

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'argSort': self.op_sort.dict,
            'sort': self.sort.dict,
            'first': self.left.dict,
            'second': self.right.dict,
        }


@final
@dataclass(frozen=True)
class Equals(BinaryPred):
    op_sort: Sort
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        op_sort: Optional[Sort] = None,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'Equals':
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Equals(op_sort=op_sort, sort=sort, left=left, right=right)

    def let_sort(self, sort: Sort) -> 'Equals':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Equals':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Equals'

    @classmethod
    def symbol(cls) -> str:
        return '\\equals'

    @classmethod
    def of(cls: Type['Equals'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Equals':
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        left, right = patterns
        return Equals(op_sort=op_sort, sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['Equals'], dct: Mapping[str, Any]) -> 'Equals':
        cls._check_tag(dct)
        return Equals(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


@final
@dataclass(frozen=True)
class In(BinaryPred):
    op_sort: Sort
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        op_sort: Optional[Sort] = None,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'In':
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return In(op_sort=op_sort, sort=sort, left=left, right=right)

    def let_sort(self, sort: Sort) -> 'In':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'In':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'In'

    @classmethod
    def symbol(cls) -> str:
        return '\\in'

    @classmethod
    def of(cls: Type['In'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'In':
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        left, right = patterns
        return In(op_sort=op_sort, sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['In'], dct: Mapping[str, Any]) -> 'In':
        cls._check_tag(dct)
        return In(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


class MLRewrite(MLPattern, WithSort):
    @property
    def sorts(self) -> Tuple[Sort]:
        return (self.sort,)


@final
@dataclass(frozen=True)
class Next(MLRewrite):
    sort: Sort
    pattern: Pattern

    def let(self, *, sort: Optional[Sort] = None, pattern: Optional[Pattern] = None) -> 'Next':
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Next(sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> 'Next':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Next':
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Next'

    @classmethod
    def symbol(cls) -> str:
        return '\\next'

    @classmethod
    def of(cls: Type['Next'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'Next':
        cls._check_symbol(symbol)
        (sort,) = sorts
        (pattern,) = patterns
        return Next(sort=sort, pattern=pattern)

    @classmethod
    def from_dict(cls: Type['Next'], dct: Mapping[str, Any]) -> 'Next':
        cls._check_tag(dct)
        return Next(
            sort=Sort.from_dict(dct['sort']),
            pattern=Pattern.from_dict(dct['dest']),
        )

    @property
    def patterns(self) -> Tuple[Pattern]:
        return (self.pattern,)

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'sort': self.sort.dict, 'dest': self.pattern.dict}


@final
@dataclass(frozen=True)
class Rewrites(MLRewrite):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Optional[Sort] = None,
        left: Optional[Pattern] = None,
        right: Optional[Pattern] = None,
    ) -> 'Rewrites':
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Rewrites(sort=sort, left=left, right=right)

    def let_sort(self, sort: Sort) -> 'Rewrites':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'Rewrites':
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Rewrites'

    @classmethod
    def symbol(cls) -> str:
        return '\\rewrites'

    @classmethod
    def of(
        cls: Type['Rewrites'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()
    ) -> 'Rewrites':
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Rewrites(sort=sort, left=left, right=right)

    @classmethod
    def from_dict(cls: Type['Rewrites'], dct: Mapping[str, Any]) -> 'Rewrites':
        cls._check_tag(dct)
        return Rewrites(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['source']),
            right=Pattern.from_dict(dct['dest']),
        )

    @property
    def patterns(self) -> Tuple[Pattern, Pattern]:
        return (self.left, self.right)

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag(),
            'sort': self.sort.dict,
            'source': self.left.dict,
            'dest': self.right.dict,
        }


@final
@dataclass(frozen=True)
class DV(MLPattern, WithSort):
    sort: Sort
    value: String  # TODO Should this be changed to str?

    def let(self, *, sort: Optional[Sort] = None, value: Optional[String] = None) -> 'DV':
        sort = sort if sort is not None else self.sort
        value = value if value is not None else self.value
        return DV(sort=sort, value=value)

    def let_sort(self, sort: Sort) -> 'DV':
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'DV':
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'DV'

    @classmethod
    def symbol(cls) -> str:
        return '\\dv'

    @classmethod
    def of(cls: Type['DV'], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> 'DV':
        cls._check_symbol(symbol)
        (sort,) = sorts
        (value,) = patterns
        value = check_type(value, String)
        return DV(sort=sort, value=value)

    @classmethod
    def from_dict(cls: Type['DV'], dct: Mapping[str, Any]) -> 'DV':
        cls._check_tag(dct)
        return DV(
            sort=Sort.from_dict(dct['sort']),
            value=String(dct['value']),
        )

    @property
    def sorts(self) -> Tuple[Sort]:
        return (self.sort,)

    @property
    def patterns(self) -> Tuple[()]:
        return ()

    @property
    def ctor_patterns(self) -> Tuple[String]:
        return (self.value,)

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'sort': self.sort.dict, 'value': self.value.value}


class MLSyntaxSugar(MLPattern):
    ...


# TODO AppAssoc, OrAssoc
class Assoc(MLSyntaxSugar):
    app: App

    @property
    @abstractmethod
    def pattern(self) -> Pattern:
        ...

    @property
    def sorts(self) -> Tuple[()]:
        return ()

    @property
    def patterns(self) -> Tuple[()]:
        return ()

    @property
    def ctor_patterns(self) -> Tuple[App]:
        return (self.app,)

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag(), 'app': self.app.dict}


@final
@dataclass(frozen=True)
class LeftAssoc(Assoc):
    app: App

    def let(self, *, app: Optional[App] = None) -> 'LeftAssoc':
        app = app if app is not None else self.app
        return LeftAssoc(app=app)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'LeftAssoc':
        () = patterns
        return self

    @property
    def pattern(self) -> Pattern:
        if len(self.app.sorts) > 0:
            raise ValueError(f'Cannot associate a pattern with sort parameters: {self}')
        if len(self.app.args) == 0:
            raise ValueError(f'Cannot associate a pattern with no arguments: {self}')
        ret = self.app.args[0]
        for a in self.app.args[1:]:
            ret = App(self.app.symbol, [], [ret, a])
        return ret

    @classmethod
    def _tag(cls) -> str:
        return 'LeftAssoc'

    @classmethod
    def symbol(cls) -> str:
        return '\\left-assoc'

    @classmethod
    def of(
        cls: Type['LeftAssoc'],
        symbol: str,
        sorts: Iterable[Sort] = (),
        patterns: Iterable[Pattern] = (),
    ) -> 'LeftAssoc':
        cls._check_symbol(symbol)
        () = sorts
        (app,) = patterns
        app = check_type(app, App)
        return LeftAssoc(app=app)

    @classmethod
    def from_dict(cls: Type['LeftAssoc'], dct: Mapping[str, Any]) -> 'LeftAssoc':
        cls._check_tag(dct)
        return LeftAssoc(app=App.from_dict(dct['app']))


@final
@dataclass(frozen=True)
class RightAssoc(Assoc):
    app: App

    def let(self, *, app: Optional[App] = None) -> 'RightAssoc':
        app = app if app is not None else self.app
        return RightAssoc(app=app)

    def let_patterns(self, patterns: Iterable[Pattern]) -> 'RightAssoc':
        () = patterns
        return self

    @property
    def pattern(self) -> Pattern:
        if len(self.app.sorts) > 0:
            raise ValueError(f'Cannot associate a pattern with sort parameters: {self}')
        if len(self.app.args) == 0:
            raise ValueError(f'Cannot associate a pattern with no arguments: {self}')
        ret = self.app.args[-1]
        for a in reversed(self.app.args[:-1]):
            ret = App(self.app.symbol, [], [a, ret])
        return ret

    @classmethod
    def _tag(cls) -> str:
        return 'RightAssoc'

    @classmethod
    def symbol(cls) -> str:
        return '\\right-assoc'

    @classmethod
    def of(
        cls: Type['RightAssoc'],
        symbol: str,
        sorts: Iterable[Sort] = (),
        patterns: Iterable[Pattern] = (),
    ) -> 'RightAssoc':
        cls._check_symbol(symbol)
        () = sorts
        (app,) = patterns
        app = check_type(app, App)
        return RightAssoc(app=app)

    @classmethod
    def from_dict(cls: Type['RightAssoc'], dct: Mapping[str, Any]) -> 'RightAssoc':
        cls._check_tag(dct)
        return RightAssoc(app=App.from_dict(dct['app']))


ML_SYMBOLS: Final = {
    r'\top': Top,
    r'\bottom': Bottom,
    r'\not': Not,
    r'\and': And,
    r'\or': Or,
    r'\implies': Implies,
    r'\iff': Iff,
    r'\exists': Exists,
    r'\forall': Forall,
    r'\mu': Mu,
    r'\nu': Nu,
    r'\ceil': Ceil,
    r'\floor': Floor,
    r'\equals': Equals,
    r'\in': In,
    r'\next': Next,
    r'\rewrites': Rewrites,
    r'\dv': DV,
    r'\left-assoc': LeftAssoc,
    r'\right-assoc': RightAssoc,
}


@final
@dataclass(frozen=True)
class Attr(Kore):  # https://github.com/runtimeverification/k/issues/3137
    symbol: str
    sorts: Tuple[Sort, ...]
    params: Tuple[Union[String, 'Attr'], ...]

    def __init__(self, symbol: str, sorts: Iterable[Sort] = (), params: Iterable[Union[String, 'Attr']] = ()):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'params', tuple(params))

    def let(
        self,
        *,
        symbol: Optional[str] = None,
        sorts: Iterable[Sort] = (),
        params: Optional[Iterable[Union[String, 'Attr']]] = None,
    ) -> 'Attr':
        symbol = symbol if symbol is not None else self.symbol
        sorts = sorts if sorts is not None else self.sorts
        params = params if params is not None else self.params
        return Attr(symbol=symbol, sorts=sorts, params=params)

    @classmethod
    def _tag(cls) -> str:
        return 'Attr'

    @classmethod
    def from_dict(cls: Type['Attr'], dct: Mapping[str, Any]) -> 'Attr':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return (
            self.symbol
            + ' '
            + _braced(sort.text for sort in self.sorts)
            + ' '
            + _parend(param.text for param in self.params)
        )


class WithAttrs(ABC):
    attrs: Tuple[App, ...]

    @abstractmethod
    def let_attrs(self: WA, attrs: Iterable[App]) -> WA:
        ...

    def map_attrs(self: WA, f: Callable[[Tuple[App, ...]], Iterable[App]]) -> WA:
        return self.let_attrs(f(self.attrs))


class Sentence(Kore, WithAttrs):
    @classmethod
    def from_dict(cls: Type['Sentence'], dct: Mapping[str, Any]) -> 'Sentence':
        return unsupported()


@final
@dataclass(frozen=True)
class Import(Sentence):
    module_name: str
    attrs: Tuple[App, ...]

    def __init__(self, module_name: str, attrs: Iterable[App] = ()):
        check_id(module_name)
        object.__setattr__(self, 'module_name', module_name)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(self, *, module_name: Optional[str] = None, attrs: Optional[Iterable[App]] = None) -> 'Import':
        module_name = module_name if module_name is not None else self.module_name
        attrs = attrs if attrs is not None else self.attrs
        return Import(module_name=module_name, attrs=attrs)

    def let_attrs(self: 'Import', attrs: Iterable[App]) -> 'Import':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'Import'

    @classmethod
    def from_dict(cls: Type['Import'], dct: Mapping[str, Any]) -> 'Import':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join(
            [
                'import',
                self.module_name,
                _brackd(attr.text for attr in self.attrs),
            ]
        )


@final
@dataclass(frozen=True)
class SortDecl(Sentence):
    name: str
    vars: Tuple[SortVar, ...]
    attrs: Tuple[App, ...]
    hooked: bool

    def __init__(self, name: str, vars: Iterable[SortVar], attrs: Iterable[App] = (), *, hooked: bool = False):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    def let(
        self,
        *,
        name: Optional[str] = None,
        vars: Optional[Iterable[SortVar]] = None,
        attrs: Optional[Iterable[App]] = None,
        hooked: Optional[bool] = None,
    ) -> 'SortDecl':
        name = name if name is not None else self.name
        vars = vars if vars is not None else self.vars
        attrs = attrs if attrs is not None else self.attrs
        hooked = hooked if hooked is not None else self.hooked
        return SortDecl(name=name, vars=vars, attrs=attrs, hooked=hooked)

    def let_attrs(self: 'SortDecl', attrs: Iterable[App]) -> 'SortDecl':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'SortDecl'

    @classmethod
    def from_dict(cls: Type['SortDecl'], dct: Mapping[str, Any]) -> 'SortDecl':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join(
            [
                'hooked-sort' if self.hooked else 'sort',
                self.name,
                _braced(var.text for var in self.vars),
                _brackd(attr.text for attr in self.attrs),
            ]
        )


@final
@dataclass(frozen=True)
class Symbol(Kore):
    name: str
    vars: Tuple[SortVar, ...]

    def __init__(self, name: str, vars: Iterable[SortVar] = ()):
        check_symbol_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))

    def let(self, *, name: Optional[str] = None, vars: Optional[Iterable[SortVar]] = None) -> 'Symbol':
        name = name if name is not None else self.name
        vars = vars if vars is not None else self.vars
        return Symbol(name=name, vars=vars)

    @classmethod
    def _tag(cls) -> str:
        return 'Symbol'

    @classmethod
    def from_dict(cls: Type['Symbol'], dct: Mapping[str, Any]) -> 'Symbol':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(var.text for var in self.vars)


@final
@dataclass(frozen=True)
class SymbolDecl(Sentence):
    symbol: Symbol
    param_sorts: Tuple[Sort, ...]
    sort: Sort
    attrs: Tuple[App, ...]
    hooked: bool

    def __init__(
        self,
        symbol: Symbol,
        param_sorts: Iterable[Sort],
        sort: Sort,
        attrs: Iterable[App] = (),
        *,
        hooked: bool = False,
    ):
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'param_sorts', tuple(param_sorts))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    def let(
        self,
        *,
        symbol: Optional[Symbol] = None,
        param_sorts: Optional[Iterable[Sort]] = None,
        sort: Optional[Sort] = None,
        attrs: Optional[Iterable[App]] = None,
        hooked: Optional[bool] = None,
    ) -> 'SymbolDecl':
        symbol = symbol if symbol is not None else self.symbol
        param_sorts = param_sorts if param_sorts is not None else self.param_sorts
        sort = sort if sort is not None else self.sort
        attrs = attrs if attrs is not None else self.attrs
        hooked = hooked if hooked is not None else self.hooked
        return SymbolDecl(symbol=symbol, param_sorts=param_sorts, sort=sort, attrs=attrs, hooked=hooked)

    def let_attrs(self: 'SymbolDecl', attrs: Iterable[App]) -> 'SymbolDecl':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'SymbolDecl'

    @classmethod
    def from_dict(cls: Type['SymbolDecl'], dct: Mapping[str, Any]) -> 'SymbolDecl':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join(
            [
                'hooked-symbol' if self.hooked else 'symbol',
                self.symbol.text,
                _parend(sort.text for sort in self.param_sorts),
                ':',
                self.sort.text,
                _brackd(attr.text for attr in self.attrs),
            ]
        )


@final
@dataclass(frozen=True)
class AliasDecl(Sentence):
    alias: Symbol
    param_sorts: Tuple[Sort, ...]
    sort: Sort
    left: App
    right: Pattern
    attrs: Tuple[App, ...]

    def __init__(
        self,
        alias: Symbol,
        param_sorts: Iterable[Sort],
        sort: Sort,
        left: App,
        right: Pattern,
        attrs: Iterable[App] = (),
    ):
        object.__setattr__(self, 'alias', alias)
        object.__setattr__(self, 'param_sorts', tuple(param_sorts))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        alias: Optional[Symbol] = None,
        param_sorts: Optional[Iterable[Sort]] = None,
        sort: Optional[Sort] = None,
        left: Optional[App] = None,
        right: Optional[Pattern] = None,
        attrs: Optional[Iterable[App]] = None,
    ) -> 'AliasDecl':
        alias = alias if alias is not None else self.alias
        param_sorts = param_sorts if param_sorts is not None else self.param_sorts
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        attrs = attrs if attrs is not None else self.attrs
        return AliasDecl(alias=alias, param_sorts=param_sorts, sort=sort, left=left, right=right, attrs=attrs)

    def let_attrs(self: 'AliasDecl', attrs: Iterable[App]) -> 'AliasDecl':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'AliasDecl'

    @classmethod
    def from_dict(cls: Type['AliasDecl'], dct: Mapping[str, Any]) -> 'AliasDecl':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join(
            [
                'alias',
                self.alias.text,
                _parend(sort.text for sort in self.param_sorts),
                ':',
                self.sort.text,
                'where',
                self.left.text,
                ':=',
                self.right.text,
                _brackd(attr.text for attr in self.attrs),
            ]
        )


class AxiomLike(Sentence):
    _label: ClassVar[str]

    vars: Tuple[SortVar, ...]
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['AxiomLike'], dct: Mapping[str, Any]) -> 'AxiomLike':
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join(
            [
                self._label,
                _braced(var.text for var in self.vars),
                self.pattern.text,
                _brackd(attr.text for attr in self.attrs),
            ]
        )


@final
@dataclass(frozen=True)
class Axiom(AxiomLike):
    _label = 'axiom'

    vars: Tuple[SortVar, ...]
    pattern: Pattern
    attrs: Tuple[App, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[App] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        vars: Optional[Iterable[SortVar]] = None,
        pattern: Optional[Pattern] = None,
        attrs: Optional[Iterable[App]] = None,
    ) -> 'Axiom':
        vars = vars if vars is not None else self.vars
        pattern = pattern if pattern is not None else self.pattern
        attrs = attrs if attrs is not None else self.attrs
        return Axiom(vars=vars, pattern=pattern, attrs=attrs)

    def let_attrs(self: 'Axiom', attrs: Iterable[App]) -> 'Axiom':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'Axiom'

    @classmethod
    def from_dict(cls: Type['Axiom'], dct: Mapping[str, Any]) -> 'Axiom':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()


@final
@dataclass(frozen=True)
class Claim(AxiomLike):
    _label = 'claim'

    vars: Tuple[SortVar, ...]
    pattern: Pattern
    attrs: Tuple[App, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[App] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        vars: Optional[Iterable[SortVar]] = None,
        pattern: Optional[Pattern] = None,
        attrs: Optional[Iterable[App]] = None,
    ) -> 'Claim':
        vars = vars if vars is not None else self.vars
        pattern = pattern if pattern is not None else self.pattern
        attrs = attrs if attrs is not None else self.attrs
        return Claim(vars=vars, pattern=pattern, attrs=attrs)

    def let_attrs(self: 'Claim', attrs: Iterable[App]) -> 'Claim':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'Claim'

    @classmethod
    def from_dict(cls: Type['Claim'], dct: Mapping[str, Any]) -> 'Claim':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()


@final
@dataclass(frozen=True)
class Module(Kore, WithAttrs, Iterable[Sentence]):
    name: str
    sentences: Tuple[Sentence, ...]
    attrs: Tuple[App, ...]

    def __init__(self, name: str, sentences: Iterable[Sentence] = (), attrs: Iterable[App] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'attrs', tuple(attrs))

    def __iter__(self) -> Iterator[Sentence]:
        return iter(self.sentences)

    def let(
        self,
        *,
        name: Optional[str] = None,
        sentences: Optional[Iterable[Sentence]] = None,
        attrs: Optional[Iterable[App]] = None,
    ) -> 'Module':
        name = name if name is not None else self.name
        sentences = sentences if sentences is not None else self.sentences
        attrs = attrs if attrs is not None else self.attrs
        return Module(name=name, sentences=sentences, attrs=attrs)

    def let_attrs(self: 'Module', attrs: Iterable[App]) -> 'Module':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'Module'

    @classmethod
    def from_dict(cls: Type['Module'], dct: Mapping[str, Any]) -> 'Module':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return '\n'.join(
            [f'module {self.name}']
            + [f'    {sentence.text}' for sentence in self.sentences]
            + ['endmodule ' + _brackd(attr.text for attr in self.attrs)]
        )

    @cached_property
    def symbol_decls(self) -> Tuple[SymbolDecl, ...]:
        return tuple(sentence for sentence in self if type(sentence) is SymbolDecl)

    @cached_property
    def axioms(self) -> Tuple[Axiom, ...]:
        return tuple(sentence for sentence in self if type(sentence) is Axiom)


@final
@dataclass(frozen=True)
class Definition(Kore, WithAttrs, Iterable[Module]):
    modules: Tuple[Module, ...]
    attrs: Tuple[App, ...]

    def __init__(self, modules: Iterable[Module] = (), attrs: Iterable[App] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'attrs', tuple(attrs))

    def __iter__(self) -> Iterator[Module]:
        return iter(self.modules)

    def let(self, *, modules: Optional[Iterable[Module]] = None, attrs: Optional[Iterable[App]] = None) -> 'Definition':
        modules = modules if modules is not None else self.modules
        attrs = attrs if attrs is not None else self.attrs
        return Definition(modules=modules, attrs=attrs)

    def let_attrs(self: 'Definition', attrs: Iterable[App]) -> 'Definition':
        return self.let(attrs=attrs)

    @classmethod
    def _tag(cls) -> str:
        return 'Definition'

    @classmethod
    def from_dict(cls: Type['Definition'], dct: Mapping[str, Any]) -> 'Definition':
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        return unsupported()

    @property
    def text(self) -> str:
        return '\n\n'.join(
            [
                _brackd(attr.text for attr in self.attrs),
            ]
            + [module.text for module in self.modules]
        )


def kore_term(dct: Mapping[str, Any], cls: Type[T] = Kore) -> T:  # type: ignore
    if dct['format'] != 'KORE':
        raise ValueError(f"Invalid format: {dct['format']}")

    if dct['version'] != 1:
        raise ValueError(f"Invalid version: {dct['version']}")

    return cls.from_dict(dct['term'])
