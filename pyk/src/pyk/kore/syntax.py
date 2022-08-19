import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
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
    }

    @classmethod
    @property
    @abstractmethod
    def _tag(cls):
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
        if tag != cls._tag:
            raise ValueError(f"Expected '{cls._tag}' as 'tag' value, found: '{tag}'")

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


class Sort(Kore, ABC):
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
    _tag = 'SortVar'

    name: str

    def __init__(self, name: str):
        check_id(name)
        object.__setattr__(self, 'name', name)

    def let(self, *, name: Optional[str] = None) -> 'SortVar':
        name = name if name is not None else self.name
        return SortVar(name=name)

    @classmethod
    def from_dict(cls: Type['SortVar'], dct: Mapping[str, Any]) -> 'SortVar':
        cls._check_tag(dct)
        return SortVar(name=dct['name'])

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'name': self.name}

    @property
    def text(self) -> str:
        return self.name


@final
@dataclass(frozen=True)
class SortApp(Sort):
    _tag = 'SortApp'

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
    def from_dict(cls: Type['SortApp'], dct: Mapping[str, Any]) -> 'SortApp':
        cls._check_tag(dct)
        return SortApp(name=dct['name'], sorts=(Sort.from_dict(arg) for arg in dct['args']))

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'name': self.name, 'args': [sort.dict for sort in self.sorts]}

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(sort.text for sort in self.sorts)


class Pattern(Kore, ABC):
    @abstractmethod
    def map_pattern(self: P, f: Callable[['Pattern'], 'Pattern']) -> P:
        ...


class VarPattern(Pattern, WithSort, ABC):
    name: str
    sort: Sort

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'name': self.name, 'sort': self.sort.dict}

    @property
    def text(self) -> str:
        return f'{self.name} : {self.sort.text}'


@final
@dataclass(frozen=True)
class EVar(VarPattern):
    _tag = 'EVar'

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

    def map_pattern(self: 'EVar', f: Callable[[Pattern], Pattern]) -> 'EVar':
        return self

    @classmethod
    def from_dict(cls: Type['EVar'], dct: Mapping[str, Any]) -> 'EVar':
        cls._check_tag(dct)
        return EVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class SVar(VarPattern):
    _tag = 'SVar'

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

    def map_pattern(self: 'SVar', f: Callable[[Pattern], Pattern]) -> 'SVar':
        return self

    @classmethod
    def from_dict(cls: Type['SVar'], dct: Mapping[str, Any]) -> 'SVar':
        cls._check_tag(dct)
        return SVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class String(Pattern):
    _tag = 'String'

    value: str

    def let(self, *, value: Optional[str] = None) -> 'String':
        value = value if value is not None else self.value
        return String(value=value)

    def map_pattern(self: 'String', f: Callable[[Pattern], Pattern]) -> 'String':
        return self

    @classmethod
    def from_dict(cls: Type['String'], dct: Mapping[str, Any]) -> 'String':
        cls._check_tag(dct)
        return String(value=dct['value'])

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'value': self.value}

    @property
    def text(self) -> str:
        return f'"{encode_kore_str(self.value)}"'


@final
@dataclass(frozen=True)
class App(Pattern):
    _tag = 'App'

    symbol: str
    sorts: Tuple[Sort, ...]
    patterns: Tuple[Pattern, ...]

    def __init__(self, symbol: str, sorts: Iterable[Sort], patterns: Iterable[Pattern]):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'patterns', tuple(patterns))

    def let(
        self,
        *,
        symbol: Optional[str] = None,
        sorts: Optional[Iterable] = None,
        patterns: Optional[Iterable] = None,
    ) -> 'App':
        symbol = symbol if symbol is not None else self.symbol
        sorts = sorts if sorts is not None else self.sorts
        patterns = patterns if patterns is not None else self.patterns
        return App(symbol=symbol, sorts=sorts, patterns=patterns)

    def map_pattern(self: 'App', f: Callable[[Pattern], Pattern]) -> 'App':
        return self.let(patterns=(f(pattern) for pattern in self.patterns))

    @classmethod
    def from_dict(cls: Type['App'], dct: Mapping[str, Any]) -> 'App':
        cls._check_tag(dct)
        return App(
            symbol=dct['name'],
            sorts=(Sort.from_dict(sort) for sort in dct['sorts']),
            patterns=(Pattern.from_dict(arg) for arg in dct['args']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'name': self.symbol,
            'sorts': [sort.dict for sort in self.sorts],
            'args': [pattern.dict for pattern in self.patterns],
        }

    @property
    def text(self) -> str:
        return (
            self.symbol
            + ' '
            + _braced(sort.text for sort in self.sorts)
            + ' '
            + _parend(pattern.text for pattern in self.patterns)
        )


class MLPattern(Pattern, ABC):
    @classmethod
    @property
    @abstractmethod
    def _symbol(cls):
        ...


class MLConn(MLPattern, WithSort, ABC):
    @property
    @abstractmethod
    def patterns(self) -> Tuple[Pattern, ...]:
        ...

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ' + _parend(pattern.text for pattern in self.patterns)


class NullaryConn(MLConn, ABC):
    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'sort': self.sort.dict}

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return ()


@final
@dataclass(frozen=True)
class Top(NullaryConn):
    _tag = 'Top'
    _symbol = '\\top'

    sort: Sort

    def let(self, *, sort: Optional[Sort] = None) -> 'Top':
        sort = sort if sort is not None else self.sort
        return Top(sort=sort)

    def let_sort(self: 'Top', sort: Sort) -> 'Top':
        return self.let(sort=sort)

    def map_pattern(self: 'Top', f: Callable[[Pattern], Pattern]) -> 'Top':
        return self

    @classmethod
    def from_dict(cls: Type['Top'], dct: Mapping[str, Any]) -> 'Top':
        cls._check_tag(dct)
        return Top(sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class Bottom(NullaryConn):
    _tag = 'Bottom'
    _symbol = '\\bottom'

    sort: Sort

    def let(self, *, sort: Optional[Sort] = None) -> 'Bottom':
        sort = sort if sort is not None else self.sort
        return Bottom(sort=sort)

    def let_sort(self: 'Bottom', sort: Sort) -> 'Bottom':
        return self.let(sort=sort)

    def map_pattern(self: 'Bottom', f: Callable[[Pattern], Pattern]) -> 'Bottom':
        return self

    @classmethod
    def from_dict(cls: Type['Bottom'], dct: Mapping[str, Any]) -> 'Bottom':
        cls._check_tag(dct)
        return Bottom(sort=Sort.from_dict(dct['sort']))


class UnaryConn(MLConn, ABC):
    pattern: Pattern

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'sort': self.sort.dict, 'arg': self.pattern.dict}

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return (self.pattern,)


@final
@dataclass(frozen=True)
class Not(UnaryConn):
    _tag = 'Not'
    _symbol = '\\not'

    sort: Sort
    pattern: Pattern

    def let(self, *, sort: Optional[Sort] = None, pattern: Optional[Pattern] = None) -> 'Not':
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Not(sort=sort, pattern=pattern)

    def let_sort(self: 'Not', sort: Sort) -> 'Not':
        return self.let(sort=sort)

    def map_pattern(self: 'Not', f: Callable[[Pattern], Pattern]) -> 'Not':
        return self.let(pattern=f(self.pattern))

    @classmethod
    def from_dict(cls: Type['Not'], dct: Mapping[str, Any]) -> 'Not':
        cls._check_tag(dct)
        return Not(sort=Sort.from_dict(dct['sort']), pattern=Pattern.from_dict(dct['arg']))


class BinaryConn(MLConn, ABC):
    left: Pattern
    right: Pattern

    def __iter__(self) -> Iterator[Pattern]:
        yield self.left
        yield self.right

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'sort': self.sort.dict,
            'first': self.left.dict,
            'second': self.right.dict,
        }

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return (self.left, self.right)


@final
@dataclass(frozen=True)
class And(BinaryConn):
    _tag = 'And'
    _symbol = '\\and'

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

    def map_pattern(self: 'And', f: Callable[[Pattern], Pattern]) -> 'And':
        return self.let(left=f(self.left), right=f(self.right))

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
    _tag = 'Or'
    _symbol = '\\or'

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

    def map_pattern(self: 'Or', f: Callable[[Pattern], Pattern]) -> 'Or':
        return self.let(left=f(self.left), right=f(self.right))

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
    _tag = 'Implies'
    _symbol = '\\implies'

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

    def map_pattern(self: 'Implies', f: Callable[[Pattern], Pattern]) -> 'Implies':
        return self.let(left=f(self.left), right=f(self.right))

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
    _tag = 'Iff'
    _symbol = '\\iff'

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

    def map_pattern(self: 'Iff', f: Callable[[Pattern], Pattern]) -> 'Iff':
        return self.let(left=f(self.left), right=f(self.right))

    @classmethod
    def from_dict(cls: Type['Iff'], dct: Mapping[str, Any]) -> 'Iff':
        cls._check_tag(dct)
        return Iff(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


class MLQuant(MLPattern, WithSort, ABC):
    sort: Sort
    var: EVar  # TODO Should this be inlined to var_name, var_sort?
    pattern: Pattern

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'sort': self.sort.dict,
            'var': self.var.name,
            'varSort': self.var.sort.dict,
            'arg': self.pattern.dict,
        }

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ' + _parend((self.var.text, self.pattern.text))


@final
@dataclass(frozen=True)
class Exists(MLQuant):
    _tag = 'Exists'
    _symbol = '\\exists'

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

    def map_pattern(self: 'Exists', f: Callable[[Pattern], Pattern]) -> 'Exists':
        return self.let(pattern=f(self.pattern))

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
    _tag = 'Forall'
    _symbol = '\\forall'

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

    def map_pattern(self: 'Forall', f: Callable[[Pattern], Pattern]) -> 'Forall':
        return self.let(pattern=f(self.pattern))

    @classmethod
    def from_dict(cls: Type['Forall'], dct: Mapping[str, Any]) -> 'Forall':
        cls._check_tag(dct)
        return Forall(
            sort=Sort.from_dict(dct['sort']),
            var=EVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=Pattern.from_dict(dct['arg']),
        )


class MLFixpoint(MLPattern, ABC):
    var: SVar  # TODO Should this be inlined to var_name, var_sort?
    pattern: Pattern

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'var': self.var.name,
            'varSort': self.var.sort.dict,
            'arg': self.pattern.dict,
        }

    @property
    def text(self) -> str:
        return self._symbol + ' { } ' + _parend((self.var.text, self.pattern.text))


@final
@dataclass(frozen=True)
class Mu(MLFixpoint):
    _tag = 'Mu'
    _symbol = '\\mu'

    var: SVar
    pattern: Pattern

    def let(self, *, var: Optional[SVar] = None, pattern: Optional[Pattern] = None) -> 'Mu':
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Mu(var=var, pattern=pattern)

    def map_pattern(self: 'Mu', f: Callable[[Pattern], Pattern]) -> 'Mu':
        return self.let(pattern=f(self.pattern))

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
    _tag = 'Nu'
    _symbol = '\\nu'

    var: SVar
    pattern: Pattern

    def let(self, *, var: Optional[SVar] = None, pattern: Optional[Pattern] = None) -> 'Nu':
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Nu(var=var, pattern=pattern)

    def map_pattern(self: 'Nu', f: Callable[[Pattern], Pattern]) -> 'Nu':
        return self.let(pattern=f(self.pattern))

    @classmethod
    def from_dict(cls: Type['Nu'], dct: Mapping[str, Any]) -> 'Nu':
        cls._check_tag(dct)
        return Nu(
            var=SVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=Pattern.from_dict(dct['arg']),
        )


class MLPred(MLPattern, WithSort, ABC):
    op_sort: Sort


class RoundPred(MLPred, ABC):
    pattern: Pattern

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'argSort': self.op_sort.dict,
            'sort': self.sort.dict,
            'arg': self.pattern.dict,
        }

    @property
    def text(self) -> str:
        return self._symbol + ' ' + _braced((self.op_sort.text, self.sort.text)) + ' ( ' + self.pattern.text + ' )'


@final
@dataclass(frozen=True)
class Ceil(RoundPred):
    _tag = 'Ceil'
    _symbol = '\\ceil'

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

    def map_pattern(self: 'Ceil', f: Callable[[Pattern], Pattern]) -> 'Ceil':
        return self.let(pattern=f(self.pattern))

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
    _tag = 'Floor'
    _symbol = '\\floor'

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

    def map_pattern(self: 'Floor', f: Callable[[Pattern], Pattern]) -> 'Floor':
        return self.let(pattern=f(self.pattern))

    @classmethod
    def from_dict(cls: Type['Floor'], dct: Mapping[str, Any]) -> 'Floor':
        cls._check_tag(dct)
        return Floor(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            pattern=Pattern.from_dict(dct['arg']),
        )


class BinaryPred(MLPred, ABC):
    left: Pattern
    right: Pattern

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'argSort': self.op_sort.dict,
            'sort': self.sort.dict,
            'first': self.left.dict,
            'second': self.right.dict,
        }

    @property
    def text(self) -> str:
        return ' '.join(
            [
                self._symbol,
                _braced((self.op_sort.text, self.sort.text)),
                _parend((self.left.text, self.right.text)),
            ]
        )


@final
@dataclass(frozen=True)
class Equals(BinaryPred):
    _tag = 'Equals'
    _symbol = '\\equals'

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

    def map_pattern(self: 'Equals', f: Callable[[Pattern], Pattern]) -> 'Equals':
        return self.let(left=f(self.left), right=f(self.right))

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
    _tag = 'In'
    _symbol = '\\in'

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

    def map_pattern(self: 'In', f: Callable[[Pattern], Pattern]) -> 'In':
        return self.let(left=f(self.left), right=f(self.right))

    @classmethod
    def from_dict(cls: Type['In'], dct: Mapping[str, Any]) -> 'In':
        cls._check_tag(dct)
        return In(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )


class MLRewrite(MLPattern, WithSort, ABC):
    ...


@final
@dataclass(frozen=True)
class Next(MLRewrite):
    _tag = 'Next'
    _symbol = '\\next'

    sort: Sort
    pattern: Pattern

    def let(self, *, sort: Optional[Sort] = None, pattern: Optional[Pattern] = None) -> 'Next':
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Next(sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> 'Next':
        return self.let(sort=sort)

    def map_pattern(self: 'Next', f: Callable[[Pattern], Pattern]) -> 'Next':
        return self.let(pattern=f(self.pattern))

    @classmethod
    def from_dict(cls: Type['Next'], dct: Mapping[str, Any]) -> 'Next':
        cls._check_tag(dct)
        return Next(
            sort=Sort.from_dict(dct['sort']),
            pattern=Pattern.from_dict(dct['dest']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'sort': self.sort.dict, 'dest': self.pattern.dict}

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ( ' + self.pattern.text + ' )'


@final
@dataclass(frozen=True)
class Rewrites(MLRewrite):
    _tag = 'Rewrites'
    _symbol = '\\rewrites'

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

    def map_pattern(self: 'Rewrites', f: Callable[[Pattern], Pattern]) -> 'Rewrites':
        return self.let(left=f(self.left), right=f(self.right))

    @classmethod
    def from_dict(cls: Type['Rewrites'], dct: Mapping[str, Any]) -> 'Rewrites':
        cls._check_tag(dct)
        return Rewrites(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['source']),
            right=Pattern.from_dict(dct['dest']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'tag': self._tag,
            'sort': self.sort.dict,
            'source': self.left.dict,
            'dest': self.right.dict,
        }

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ' + _parend((self.left.text, self.right.text))


@final
@dataclass(frozen=True)
class DV(MLPattern, WithSort):
    _tag = 'DV'
    _symbol = '\\dv'

    sort: Sort
    value: String  # TODO Should this be changed to str?

    def let(self, *, sort: Optional[Sort] = None, value: Optional[String] = None) -> 'DV':
        sort = sort if sort is not None else self.sort
        value = value if value is not None else self.value
        return DV(sort=sort, value=value)

    def let_sort(self, sort: Sort) -> 'DV':
        return self.let(sort=sort)

    def map_pattern(self: 'DV', f: Callable[[Pattern], Pattern]) -> 'DV':
        return self

    @classmethod
    def from_dict(cls: Type['DV'], dct: Mapping[str, Any]) -> 'DV':
        cls._check_tag(dct)
        return DV(
            sort=Sort.from_dict(dct['sort']),
            value=String(dct['value']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        return {'tag': self._tag, 'sort': self.sort.dict, 'value': self.value.value}

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ( ' + self.value.text + ' )'


# TODO
class MLSyntaxSugar(MLPattern, ABC):
    ...


@final
@dataclass(frozen=True)
class Attr(Kore):
    symbol: str
    params: Tuple[Union[String, 'Attr'], ...]

    def __init__(self, symbol: str, params: Iterable[Union[String, 'Attr']] = ()):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'params', tuple(params))

    def let(self, *, symbol: Optional[str] = None, params: Optional[Iterable[Union[String, 'Attr']]] = None) -> 'Attr':
        symbol = symbol if symbol is not None else self.symbol
        params = params if params is not None else self.params
        return Attr(symbol=symbol, params=params)

    @classmethod
    @property
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
        return self.symbol + ' { } ' + _parend(param.text for param in self.params)


class WithAttrs(ABC):
    attrs: Tuple[Attr, ...]

    @abstractmethod
    def let_attrs(self: WA, attrs: Iterable[Attr]) -> WA:
        ...

    def map_attrs(self: WA, f: Callable[[Tuple[Attr, ...]], Iterable[Attr]]) -> WA:
        return self.let_attrs(f(self.attrs))


class Sentence(Kore, WithAttrs, ABC):
    @classmethod
    def from_dict(cls: Type['Sentence'], dct: Mapping[str, Any]) -> 'Sentence':
        return unsupported()


@final
@dataclass(frozen=True)
class Import(Sentence):
    module_name: str
    attrs: Tuple[Attr, ...]

    def __init__(self, module_name: str, attrs: Iterable[Attr] = ()):
        check_id(module_name)
        object.__setattr__(self, 'module_name', module_name)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(self, *, module_name: Optional[str] = None, attrs: Optional[Iterable[Attr]] = None) -> 'Import':
        module_name = module_name if module_name is not None else self.module_name
        attrs = attrs if attrs is not None else self.attrs
        return Import(module_name=module_name, attrs=attrs)

    def let_attrs(self: 'Import', attrs: Iterable[Attr]) -> 'Import':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
    attrs: Tuple[Attr, ...]
    hooked: bool

    def __init__(self, name: str, vars: Iterable[SortVar], attrs: Iterable[Attr] = (), *, hooked=False):
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
        attrs: Optional[Iterable[Attr]] = None,
        hooked: Optional[bool] = None,
    ) -> 'SortDecl':
        name = name if name is not None else self.name
        vars = vars if vars is not None else self.vars
        attrs = attrs if attrs is not None else self.attrs
        return SortDecl(name=name, vars=vars, attrs=attrs, hooked=hooked)

    def let_attrs(self: 'SortDecl', attrs: Iterable[Attr]) -> 'SortDecl':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
    @property
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
    sort_params: Tuple[Sort, ...]
    sort: Sort
    attrs: Tuple[Attr, ...]
    hooked: bool

    def __init__(
        self, symbol: Symbol, sort_params: Iterable[Sort], sort: Sort, attrs: Iterable[Attr] = (), *, hooked=False
    ):
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    def let(
        self,
        *,
        symbol: Optional[Symbol] = None,
        sort_params: Optional[Iterable[Sort]] = None,
        sort: Optional[Sort] = None,
        attrs: Optional[Iterable[Attr]] = None,
        hooked: Optional[bool] = None,
    ) -> 'SymbolDecl':
        symbol = symbol if symbol is not None else self.symbol
        sort_params = sort_params if sort_params is not None else self.sort_params
        sort = sort if sort is not None else self.sort
        attrs = attrs if attrs is not None else self.attrs
        hooked = hooked if hooked is not None else self.hooked
        return SymbolDecl(symbol=symbol, sort_params=sort_params, sort=sort, attrs=attrs, hooked=hooked)

    def let_attrs(self: 'SymbolDecl', attrs: Iterable[Attr]) -> 'SymbolDecl':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
                _parend(sort.text for sort in self.sort_params),
                ':',
                self.sort.text,
                _brackd(attr.text for attr in self.attrs),
            ]
        )


@final
@dataclass(frozen=True)
class AliasDecl(Sentence):
    alias: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    left: App
    right: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(
        self,
        alias: Symbol,
        sort_params: Iterable[Sort],
        sort: Sort,
        left: App,
        right: Pattern,
        attrs: Iterable[Attr] = (),
    ):
        object.__setattr__(self, 'alias', alias)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        alias: Optional[Symbol] = None,
        sort_params: Optional[Iterable[Sort]] = None,
        sort: Optional[Sort] = None,
        left: Optional[App] = None,
        right: Optional[Pattern] = None,
        attrs: Optional[Iterable[Attr]] = None,
    ) -> 'AliasDecl':
        alias = alias if alias is not None else self.alias
        sort_params = sort_params if sort_params is not None else self.sort_params
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        attrs = attrs if attrs is not None else self.attrs
        return AliasDecl(alias=alias, sort_params=sort_params, sort=sort, left=left, right=right, attrs=attrs)

    def let_attrs(self: 'AliasDecl', attrs: Iterable[Attr]) -> 'AliasDecl':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
                _parend(sort.text for sort in self.sort_params),
                ':',
                self.sort.text,
                'where',
                self.left.text,
                ':=',
                self.right.text,
                _brackd(attr.text for attr in self.attrs),
            ]
        )


class AxiomLike(Sentence, ABC):
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
    attrs: Tuple[Attr, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        vars: Optional[Iterable[SortVar]] = None,
        pattern: Optional[Pattern] = None,
        attrs: Optional[Iterable[Attr]] = None,
    ) -> 'Axiom':
        vars = vars if vars is not None else self.vars
        pattern = pattern if pattern is not None else self.pattern
        attrs = attrs if attrs is not None else self.attrs
        return Axiom(vars=vars, pattern=pattern, attrs=attrs)

    def let_attrs(self: 'Axiom', attrs: Iterable[Attr]) -> 'Axiom':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
    attrs: Tuple[Attr, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        vars: Optional[Iterable[SortVar]] = None,
        pattern: Optional[Pattern] = None,
        attrs: Optional[Iterable[Attr]] = None,
    ) -> 'Claim':
        vars = vars if vars is not None else self.vars
        pattern = pattern if pattern is not None else self.pattern
        attrs = attrs if attrs is not None else self.attrs
        return Claim(vars=vars, pattern=pattern, attrs=attrs)

    def let_attrs(self: 'Claim', attrs: Iterable[Attr]) -> 'Claim':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
class Module(Kore, WithAttrs):
    name: str
    sentences: Tuple[Sentence, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, name: str, sentences: Iterable[Sentence] = (), attrs: Iterable[Attr] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        name: Optional[str] = None,
        sentences: Optional[Iterable[Sentence]] = None,
        attrs: Optional[Iterable[Attr]] = None,
    ) -> 'Module':
        name = name if name is not None else self.name
        sentences = sentences if sentences is not None else self.sentences
        attrs = attrs if attrs is not None else self.attrs
        return Module(name=name, sentences=sentences, attrs=attrs)

    def let_attrs(self: 'Module', attrs: Iterable[Attr]) -> 'Module':
        return self.let(attrs=attrs)

    @classmethod
    @property
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


@final
@dataclass(frozen=True)
class Definition(Kore, WithAttrs):
    modules: Tuple[Module, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, modules: Iterable[Module] = (), attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self, *, modules: Optional[Iterable[Module]] = None, attrs: Optional[Iterable[Attr]] = None
    ) -> 'Definition':
        modules = modules if modules is not None else self.modules
        attrs = attrs if attrs is not None else self.attrs
        return Definition(modules=modules, attrs=attrs)

    def let_attrs(self: 'Definition', attrs: Iterable[Attr]) -> 'Definition':
        return self.let(attrs=attrs)

    @classmethod
    @property
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
