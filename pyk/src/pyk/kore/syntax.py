from __future__ import annotations

import json
import re
from abc import ABC, abstractmethod
from collections.abc import Iterable
from dataclasses import dataclass
from functools import cached_property
from io import StringIO
from typing import ClassVar  # noqa: TC003
from typing import TYPE_CHECKING, final

from ..dequote import enquoted
from ..utils import check_type

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator, Mapping
    from typing import IO, Any, Final, TypeVar

    T = TypeVar('T', bound='Kore')
    P = TypeVar('P', bound='Pattern')
    WS = TypeVar('WS', bound='WithSort')
    WA = TypeVar('WA', bound='WithAttrs')
    ML = TypeVar('ML', bound='MLPattern')


@final
@dataclass(frozen=True)
class Id:
    value: str

    _PATTERN_STR: ClassVar = "[a-zA-Z][0-9a-zA-Z'-]*"
    _PATTERN: ClassVar = re.compile(_PATTERN_STR)

    def __init__(self, value: str):
        self._check(value)
        object.__setattr__(self, 'value', value)

    @staticmethod
    def _check(value: str) -> None:
        if not Id._PATTERN.fullmatch(value):
            raise ValueError(f'Expected identifier, got: {value}')


@final
@dataclass(frozen=True)
class SymbolId:
    value: str

    _PATTERN: ClassVar = re.compile(fr'\\?{Id._PATTERN_STR}')

    def __init__(self, value: str):
        self._check(value)
        object.__setattr__(self, 'value', value)

    @staticmethod
    def _check(value: str) -> None:
        if not SymbolId._PATTERN.fullmatch(value):
            raise ValueError(f'Expected symbol identifier, got: {value}')


@final
@dataclass(frozen=True)
class SetVarId:
    value: str

    _PATTERN: ClassVar = re.compile(f'@{Id._PATTERN_STR}')

    def __init__(self, value: str):
        self._check(value)
        object.__setattr__(self, 'value', value)

    @staticmethod
    def _check(value: str) -> None:
        if not SetVarId._PATTERN.fullmatch(value):
            raise ValueError(f'Expected set variable identifier, got: {value}')


# TODO Constructor @overloads


class Kore(ABC):
    @property
    def text(self) -> str:
        str_io = StringIO()
        self.write(str_io)
        return str_io.getvalue()

    @abstractmethod
    def write(self, output: IO[str]) -> None: ...


def _write_sep_by_comma(kores: Iterable[Kore], output: IO[str]) -> None:
    first = True
    for kore in kores:
        if first:
            first = False
            kore.write(output)
        else:
            output.write(', ')
            kore.write(output)


class Sort(Kore):
    name: str

    @property
    def json(self) -> str:
        return json.dumps(self.dict, sort_keys=True)

    @property
    @abstractmethod
    def dict(self) -> dict[str, Any]: ...

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> Sort:
        tag = dct['tag']
        match tag:
            case 'SortVar':
                return SortVar(name=dct['name'])
            case 'SortApp':
                return SortApp(name=dct['name'], sorts=tuple(Sort.from_dict(arg) for arg in dct['args']))
            case _:
                raise ValueError(f'Unknown Sort tag value: {tag!r}')

    @staticmethod
    def from_json(s: str) -> Sort:
        return Sort.from_dict(json.loads(s))


class WithSort(ABC):
    sort: Sort

    @abstractmethod
    def let_sort(self: WS, sort: Sort) -> WS: ...

    def map_sort(self: WS, f: Callable[[Sort], Sort]) -> WS:
        return self.let_sort(f(self.sort))


@final
@dataclass(frozen=True)
class SortVar(Sort):
    name: str

    def __init__(self, name: str | Id):
        if isinstance(name, str):
            name = Id(name)

        object.__setattr__(self, 'name', name.value)

    def let(self, *, name: str | Id | None = None) -> SortVar:
        name = name if name is not None else self.name
        return SortVar(name=name)

    @property
    def dict(self) -> dict[str, Any]:
        return {'tag': 'SortVar', 'name': self.name}

    def write(self, output: IO[str]) -> None:
        output.write(self.name)


@final
@dataclass(frozen=True)
class SortApp(Sort):
    name: str
    sorts: tuple[Sort, ...]

    def __init__(self, name: str | Id, sorts: Iterable[Sort] = ()):
        if isinstance(name, str):
            name = Id(name)

        object.__setattr__(self, 'name', name.value)
        object.__setattr__(self, 'sorts', tuple(sorts))

    def let(self, *, name: str | Id | None = None, sorts: Iterable[Sort] | None = None) -> SortApp:
        name = name if name is not None else self.name
        sorts = sorts if sorts is not None else self.sorts
        return SortApp(name=name, sorts=sorts)

    @property
    def dict(self) -> dict[str, Any]:
        return {'tag': 'SortApp', 'name': self.name, 'args': [sort.dict for sort in self.sorts]}

    def write(self, output: IO[str]) -> None:
        output.write(self.name)
        output.write('{')
        _write_sep_by_comma(self.sorts, output)
        output.write('}')


class Pattern(Kore):
    _TAGS: Final[dict[str, str | list[str]]] = {
        # Helper structure for from_dict(dct)
        # keys are Pattern subclass names, which coincides with the tag 'field' in dct
        # list value indicates fields in dct that transform to Pattern
        # str value indicates a field in dct that transforms to list[Pattern]
        'String': [],
        'EVar': [],
        'SVar': [],
        'App': 'args',
        'Top': [],
        'Bottom': [],
        'Not': ['arg'],
        'Implies': ['first', 'second'],
        'Iff': ['first', 'second'],
        'And': 'patterns',
        'Or': 'patterns',
        'Exists': ['arg'],
        'Forall': ['arg'],
        'Mu': ['arg'],
        'Nu': ['arg'],
        'Ceil': ['arg'],
        'Floor': ['arg'],
        'Equals': ['first', 'second'],
        'In': ['first', 'second'],
        'Next': ['dest'],
        'Rewrites': ['source', 'dest'],
        'DV': [],
        'LeftAssoc': 'argss',
        'RightAssoc': 'argss',
    }

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> Pattern:
        stack: list = [dct, Pattern._extract_dicts(dct), []]
        while True:
            patterns = stack[-1]
            dcts = stack[-2]
            dct = stack[-3]
            idx = len(patterns) - len(dcts)
            if not idx:
                stack.pop()
                stack.pop()
                stack.pop()
                cls = globals()[dct['tag']]
                pattern = cls._from_dict(dct, patterns)
                if not stack:
                    return pattern
                stack[-1].append(pattern)
            else:
                dct = dcts[idx]
                stack.append(dct)
                stack.append(Pattern._extract_dicts(dct))
                stack.append([])

    @staticmethod
    def _extract_dicts(dct: Mapping[str, Any]) -> list[Mapping[str, Any]]:
        keys = Pattern._TAGS[dct['tag']]
        return dct[keys] if isinstance(keys, str) else [dct[key] for key in keys]

    @staticmethod
    def from_json(s: str) -> Pattern:
        return Pattern.from_dict(json.loads(s))

    @classmethod
    @abstractmethod
    def _from_dict(cls: type[P], dct: Mapping[str, Any], patterns: list[Pattern]) -> P: ...

    @property
    def json(self) -> str:
        return json.dumps(self.dict, sort_keys=True)

    @abstractmethod
    def _dict(self, dicts: list) -> dict[str, Any]: ...

    @classmethod
    @abstractmethod
    def _tag(cls) -> str:  # TODO This should be an abstract immutable class attribute for efficiency
        ...

    @final
    @property
    def dict(self) -> dict[str, Any]:
        stack: list = [
            self,
            self.patterns,
            [],
        ]

        while True:
            dicts = stack[-1]
            patterns = stack[-2]
            pattern = stack[-3]
            idx = len(dicts) - len(patterns)
            if not idx:
                stack.pop()
                stack.pop()
                stack.pop()
                dct = pattern._dict(dicts)
                if not stack:
                    return dct
                stack[-1].append(dct)
            else:
                pattern = patterns[idx]
                stack.append(pattern)
                stack.append(pattern.patterns)
                stack.append([])

    @property
    @abstractmethod
    def patterns(self) -> tuple[Pattern, ...]: ...

    @abstractmethod
    def let_patterns(self: P, patterns: Iterable[Pattern]) -> P: ...

    def map_patterns(self: P, f: Callable[[Pattern], Pattern]) -> P:
        return self.let_patterns(patterns=(f(pattern) for pattern in self.patterns))

    def bottom_up(self, f: Callable[[Pattern], Pattern]) -> Pattern:
        stack: list = [self, []]
        while True:
            patterns = stack[-1]
            pattern = stack[-2]
            idx = len(patterns) - len(pattern.patterns)
            if not idx:
                stack.pop()
                stack.pop()
                pattern = f(pattern.let_patterns(patterns))
                if not stack:
                    return pattern
                stack[-1].append(pattern)
            else:
                stack.append(pattern.patterns[idx])
                stack.append([])

    def top_down(self, f: Callable[[Pattern], Pattern]) -> Pattern:
        stack: list = [f(self), []]
        while True:
            patterns = stack[-1]
            pattern = stack[-2]
            idx = len(patterns) - len(pattern.patterns)
            if not idx:
                stack.pop()
                stack.pop()
                pattern = pattern.let_patterns(patterns)
                if not stack:
                    return pattern
                stack[-1].append(pattern)
            else:
                stack.append(f(pattern.patterns[idx]))
                stack.append([])


class VarPattern(Pattern, WithSort):
    __match_args__ = ('name', 'sort')

    name: str
    sort: Sort

    @property
    def patterns(self) -> tuple[()]:
        return ()

    def _dict(self, dicts: list) -> dict[str, Any]:
        assert not dicts
        return {'tag': self._tag(), 'name': self.name, 'sort': self.sort.dict}

    def write(self, output: IO[str]) -> None:
        output.write(self.name)
        output.write(' : ')
        self.sort.write(output)


@final
@dataclass(frozen=True)
class EVar(VarPattern):
    name: str
    sort: Sort

    def __init__(self, name: str | Id, sort: Sort):
        if isinstance(name, str):
            name = Id(name)

        object.__setattr__(self, 'name', name.value)
        object.__setattr__(self, 'sort', sort)

    def let(self, *, name: str | Id | None = None, sort: Sort | None = None) -> EVar:
        name = name if name is not None else self.name
        sort = sort if sort is not None else self.sort
        return EVar(name=name, sort=sort)

    def let_sort(self, sort: Sort) -> EVar:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> EVar:
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'EVar'

    @classmethod
    def _from_dict(cls: type[EVar], dct: Mapping[str, Any], patterns: list[Pattern]) -> EVar:
        assert not patterns
        return EVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class SVar(VarPattern):
    name: str
    sort: Sort

    def __init__(self, name: str | SetVarId, sort: Sort):
        if isinstance(name, str):
            name = SetVarId(name)

        object.__setattr__(self, 'name', name.value)
        object.__setattr__(self, 'sort', sort)

    def let(self, *, name: str | SetVarId | None = None, sort: Sort | None = None) -> SVar:
        name = name if name is not None else self.name
        sort = sort if sort is not None else self.sort
        return SVar(name=name, sort=sort)

    def let_sort(self, sort: Sort) -> SVar:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> SVar:
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'SVar'

    @classmethod
    def _from_dict(cls: type[SVar], dct: Mapping[str, Any], patterns: list[Pattern]) -> SVar:
        assert not patterns
        return SVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class String(Pattern):
    value: str

    def let(self, *, value: str | None = None) -> String:
        value = value if value is not None else self.value
        return String(value=value)

    def let_patterns(self, patterns: Iterable[Pattern]) -> String:
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'String'

    @classmethod
    def _from_dict(cls: type[String], dct: Mapping[str, Any], patterns: list[Pattern]) -> String:
        assert not patterns
        return String(value=dct['value'])

    @property
    def patterns(self) -> tuple[()]:
        return ()

    def _dict(self, dicts: list) -> dict[str, Any]:
        assert not dicts
        return {'tag': 'String', 'value': self.value}

    def write(self, output: IO[str]) -> None:
        output.write('"')
        for char in enquoted(self.value):
            output.write(char)
        output.write('"')


@final
@dataclass(frozen=True)
class App(Pattern):
    symbol: str
    sorts: tuple[Sort, ...]
    args: tuple[Pattern, ...]

    def __init__(self, symbol: str | SymbolId, sorts: Iterable[Sort] = (), args: Iterable[Pattern] = ()):
        if isinstance(symbol, str):
            symbol = SymbolId(symbol)

        object.__setattr__(self, 'symbol', symbol.value)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'args', tuple(args))

    def let(
        self,
        *,
        symbol: str | SymbolId | None = None,
        sorts: Iterable | None = None,
        args: Iterable | None = None,
    ) -> App:
        symbol = symbol if symbol is not None else self.symbol
        sorts = sorts if sorts is not None else self.sorts
        args = args if args is not None else self.args
        return App(symbol=symbol, sorts=sorts, args=args)

    def let_patterns(self, patterns: Iterable[Pattern]) -> App:
        return self.let(args=patterns)

    @classmethod
    def _tag(cls) -> str:
        return 'App'

    @classmethod
    def _from_dict(cls: type[App], dct: Mapping[str, Any], patterns: list[Pattern]) -> App:
        return App(
            symbol=dct['name'],
            sorts=tuple(Sort.from_dict(sort) for sort in dct['sorts']),
            args=patterns,
        )

    @property
    def patterns(self) -> tuple[Pattern, ...]:
        return self.args

    def _dict(self, dicts: list) -> dict[str, Any]:
        return {
            'tag': 'App',
            'name': self.symbol,
            'sorts': [sort.dict for sort in self.sorts],
            'args': dicts,
        }

    def write(self, output: IO[str]) -> None:
        output.write(self.symbol)
        output.write('{')
        _write_sep_by_comma(self.sorts, output)
        output.write('}(')
        _write_sep_by_comma(self.args, output)
        output.write(')')


class Assoc(Pattern):
    symbol: str
    sorts: tuple[Sort, ...]
    args: tuple[Pattern, ...]

    @classmethod
    @abstractmethod
    def kore_symbol(cls) -> str: ...

    @property
    @abstractmethod
    def pattern(self) -> Pattern: ...

    @property
    def patterns(self) -> tuple[Pattern, ...]:
        return self.args

    @cached_property
    def app(self) -> App:
        return App(symbol=self.symbol, sorts=self.sorts, args=self.args)

    def _dict(self, dicts: list) -> dict[str, Any]:
        return {
            'tag': self._tag(),
            'symbol': self.symbol,
            'sorts': [sort.dict for sort in self.sorts],
            'argss': dicts,
        }

    def write(self, output: IO[str]) -> None:
        output.write(self.kore_symbol())
        output.write('{}(')
        self.app.write(output)
        output.write(')')


@final
@dataclass(frozen=True)
class LeftAssoc(Assoc):
    symbol: str
    sorts: tuple[Sort, ...]
    args: tuple[Pattern, ...]

    def __init__(self, symbol: str | SymbolId, sorts: Iterable[Sort] = (), args: Iterable[Pattern] = ()):
        if isinstance(symbol, str):
            symbol = SymbolId(symbol)

        args = tuple(args)
        if not args:
            raise ValueError("Expected non-empty iterable for 'args'")

        object.__setattr__(self, 'symbol', symbol.value)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'args', args)

    def let(
        self,
        *,
        symbol: str | SymbolId | None = None,
        sorts: Iterable | None = None,
        args: Iterable | None = None,
    ) -> LeftAssoc:
        symbol = symbol if symbol is not None else self.symbol
        sorts = sorts if sorts is not None else self.sorts
        args = args if args is not None else self.args
        return LeftAssoc(symbol=symbol, sorts=sorts, args=args)

    def let_patterns(self, patterns: Iterable[Pattern]) -> LeftAssoc:
        return self.let(args=patterns)

    @property
    def pattern(self) -> Pattern:
        res = self.args[0]
        for arg in self.args[1:]:
            res = App(self.symbol, self.sorts, (res, arg))
        return res

    @classmethod
    def _tag(cls) -> str:
        return 'LeftAssoc'

    @classmethod
    def kore_symbol(cls) -> str:
        return '\\left-assoc'

    @classmethod
    def _from_dict(cls: type[LeftAssoc], dct: Mapping[str, Any], patterns: list[Pattern]) -> LeftAssoc:
        return LeftAssoc(
            symbol=dct['symbol'],
            sorts=tuple(Sort.from_dict(sort) for sort in dct['sorts']),
            args=patterns,
        )


@final
@dataclass(frozen=True)
class RightAssoc(Assoc):
    symbol: str
    sorts: tuple[Sort, ...]
    args: tuple[Pattern, ...]

    def __init__(self, symbol: str | SymbolId, sorts: Iterable[Sort] = (), args: Iterable[Pattern] = ()):
        if isinstance(symbol, str):
            symbol = SymbolId(symbol)

        args = tuple(args)
        if not args:
            raise ValueError("Expected non-empty iterable for 'args'")

        object.__setattr__(self, 'symbol', symbol.value)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'args', args)

    def let(
        self,
        *,
        symbol: str | SymbolId | None = None,
        sorts: Iterable | None = None,
        args: Iterable | None = None,
    ) -> RightAssoc:
        symbol = symbol if symbol is not None else self.symbol
        sorts = sorts if sorts is not None else self.sorts
        args = args if args is not None else self.args
        return RightAssoc(symbol=symbol, sorts=sorts, args=args)

    def let_patterns(self, patterns: Iterable[Pattern]) -> RightAssoc:
        return self.let(args=patterns)

    @property
    def pattern(self) -> Pattern:
        res = self.args[-1]
        for arg in reversed(self.args[:-1]):
            res = App(self.symbol, (), (arg, res))
        return res

    @classmethod
    def _tag(cls) -> str:
        return 'RightAssoc'

    @classmethod
    def kore_symbol(cls) -> str:
        return '\\right-assoc'

    @classmethod
    def _from_dict(cls: type[RightAssoc], dct: Mapping[str, Any], patterns: list[Pattern]) -> RightAssoc:
        return RightAssoc(
            symbol=dct['symbol'],
            sorts=tuple(Sort.from_dict(sort) for sort in dct['sorts']),
            args=patterns,
        )


class MLPattern(Pattern):
    @classmethod
    @abstractmethod
    def symbol(cls) -> str: ...

    @classmethod
    def of(cls: type[ML], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> ML:
        actual_cls = ML_SYMBOLS.get(symbol)

        if not actual_cls:
            raise ValueError(f'Invalid MLPattern symbol: {symbol}')

        if not issubclass(actual_cls, cls):
            raise ValueError(f'Expected {cls.__name__} symbol, found: {symbol}')

        return actual_cls.of(symbol, sorts, patterns)

    @classmethod
    def _check_symbol(cls: type[ML], symbol: str) -> None:
        if symbol != cls.symbol():
            raise ValueError(f'Expected "symbol" value: {cls.symbol()}, got: {symbol}')

    @property
    @abstractmethod
    def sorts(self) -> tuple[Sort, ...]: ...

    @property
    def ctor_patterns(self) -> tuple[Pattern, ...]:
        """Return patterns used to construct the term with `of`.

        Except for `DV`, `MLFixpoint` and `MLQuant` this coincides with `patterns`.
        """
        return self.patterns

    def write(self, output: IO[str]) -> None:
        output.write(self.symbol())
        output.write('{')
        _write_sep_by_comma(self.sorts, output)
        output.write('}(')
        _write_sep_by_comma(self.ctor_patterns, output)
        output.write(')')


class MLConn(MLPattern, WithSort):
    @property
    def sorts(self) -> tuple[Sort]:
        return (self.sort,)


class NullaryConn(MLConn):
    def _dict(self, dicts: list) -> dict[str, Any]:
        assert not dicts
        return {'tag': self._tag(), 'sort': self.sort.dict}

    @property
    def patterns(self) -> tuple[()]:
        return ()


@final
@dataclass(frozen=True)
class Top(NullaryConn):
    sort: Sort

    def let(self, *, sort: Sort | None = None) -> Top:
        sort = sort if sort is not None else self.sort
        return Top(sort=sort)

    def let_sort(self: Top, sort: Sort) -> Top:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Top:
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'Top'

    @classmethod
    def symbol(cls) -> str:
        return '\\top'

    @classmethod
    def of(cls: type[Top], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Top:
        cls._check_symbol(symbol)
        (sort,) = sorts
        () = patterns
        return Top(sort=sort)

    @classmethod
    def _from_dict(cls: type[Top], dct: Mapping[str, Any], patterns: list[Pattern]) -> Top:
        assert not patterns
        return Top(sort=Sort.from_dict(dct['sort']))


@final
@dataclass(frozen=True)
class Bottom(NullaryConn):
    sort: Sort

    def let(self, *, sort: Sort | None = None) -> Bottom:
        sort = sort if sort is not None else self.sort
        return Bottom(sort=sort)

    def let_sort(self: Bottom, sort: Sort) -> Bottom:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Bottom:
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'Bottom'

    @classmethod
    def symbol(cls) -> str:
        return '\\bottom'

    @classmethod
    def of(cls: type[Bottom], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Bottom:
        cls._check_symbol(symbol)
        (sort,) = sorts
        () = patterns
        return Bottom(sort=sort)

    @classmethod
    def _from_dict(cls: type[Bottom], dct: Mapping[str, Any], patterns: list[Pattern]) -> Bottom:
        assert not patterns
        return Bottom(sort=Sort.from_dict(dct['sort']))


class UnaryConn(MLConn):
    pattern: Pattern

    @property
    def patterns(self) -> tuple[Pattern]:
        return (self.pattern,)

    def _dict(self, dicts: list) -> dict[str, Any]:
        (arg,) = dicts
        return {'tag': self._tag(), 'sort': self.sort.dict, 'arg': arg}


@final
@dataclass(frozen=True)
class Not(UnaryConn):
    sort: Sort
    pattern: Pattern

    def let(self, *, sort: Sort | None = None, pattern: Pattern | None = None) -> Not:
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Not(sort=sort, pattern=pattern)

    def let_sort(self: Not, sort: Sort) -> Not:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Not:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Not'

    @classmethod
    def symbol(cls) -> str:
        return '\\not'

    @classmethod
    def of(cls: type[Not], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Not:
        cls._check_symbol(symbol)
        (sort,) = sorts
        (pattern,) = patterns
        return Not(sort=sort, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Not], dct: Mapping[str, Any], patterns: list[Pattern]) -> Not:
        (pattern,) = patterns
        return Not(sort=Sort.from_dict(dct['sort']), pattern=pattern)


class BinaryConn(MLConn):
    left: Pattern
    right: Pattern

    def __iter__(self) -> Iterator[Pattern]:
        yield self.left
        yield self.right

    @property
    def patterns(self) -> tuple[Pattern, Pattern]:
        return (self.left, self.right)

    def _dict(self, dicts: list) -> dict[str, Any]:
        first, second = dicts
        return {'tag': self._tag(), 'sort': self.sort.dict, 'first': first, 'second': second}


@final
@dataclass(frozen=True)
class Implies(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Sort | None = None,
        left: Pattern | None = None,
        right: Pattern | None = None,
    ) -> Implies:
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Implies(sort=sort, left=left, right=right)

    def let_sort(self: Implies, sort: Sort) -> Implies:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Implies:
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Implies'

    @classmethod
    def symbol(cls) -> str:
        return '\\implies'

    @classmethod
    def of(cls: type[Implies], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Implies:
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Implies(sort=sort, left=left, right=right)

    @classmethod
    def _from_dict(cls: type[Implies], dct: Mapping[str, Any], patterns: list[Pattern]) -> Implies:
        left, right = patterns
        return Implies(sort=Sort.from_dict(dct['sort']), left=left, right=right)


@final
@dataclass(frozen=True)
class Iff(BinaryConn):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Sort | None = None,
        left: Pattern | None = None,
        right: Pattern | None = None,
    ) -> Iff:
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Iff(sort=sort, left=left, right=right)

    def let_sort(self: Iff, sort: Sort) -> Iff:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Iff:
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Iff'

    @classmethod
    def symbol(cls) -> str:
        return '\\iff'

    @classmethod
    def of(cls: type[Iff], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Iff:
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Iff(sort=sort, left=left, right=right)

    @classmethod
    def _from_dict(cls: type[Iff], dct: Mapping[str, Any], patterns: list[Pattern]) -> Iff:
        left, right = patterns
        return Iff(sort=Sort.from_dict(dct['sort']), left=left, right=right)


class MultiaryConn(MLConn):
    ops: tuple[Pattern, ...]

    def __iter__(self) -> Iterator[Pattern]:
        return iter(self.ops)

    @property
    def patterns(self) -> tuple[Pattern, ...]:
        return self.ops

    def _dict(self, dicts: list) -> dict[str, Any]:
        return {'tag': self._tag(), 'sort': self.sort.dict, 'patterns': dicts}


@final
@dataclass(frozen=True)
class And(MultiaryConn):
    sort: Sort
    ops: tuple[Pattern, ...]

    def __init__(self, sort: Sort, ops: Iterable[Pattern] = ()):
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'ops', tuple(ops))

    def let(
        self,
        *,
        sort: Sort | None = None,
        ops: Iterable[Pattern] | None = None,
    ) -> And:
        sort = sort if sort is not None else self.sort
        ops = ops if ops is not None else self.ops
        return And(sort=sort, ops=ops)

    def let_sort(self, sort: Sort) -> And:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> And:
        return self.let(ops=patterns)

    @classmethod
    def _tag(cls) -> str:
        return 'And'

    @classmethod
    def symbol(cls) -> str:
        return '\\and'

    @classmethod
    def of(cls: type[And], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> And:
        cls._check_symbol(symbol)
        (sort,) = sorts
        return And(sort=sort, ops=patterns)

    @classmethod
    def _from_dict(cls: type[And], dct: Mapping[str, Any], patterns: list[Pattern]) -> And:
        return And(sort=Sort.from_dict(dct['sort']), ops=patterns)


@final
@dataclass(frozen=True)
class Or(MultiaryConn):
    sort: Sort
    ops: tuple[Pattern, ...]

    def __init__(self, sort: Sort, ops: Iterable[Pattern] = ()):
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'ops', tuple(ops))

    def let(
        self,
        *,
        sort: Sort | None = None,
        ops: Iterable[Pattern] | None = None,
    ) -> Or:
        sort = sort if sort is not None else self.sort
        ops = ops if ops is not None else self.ops
        return Or(sort=sort, ops=ops)

    def let_sort(self, sort: Sort) -> Or:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Or:
        return self.let(ops=patterns)

    @classmethod
    def _tag(cls) -> str:
        return 'Or'

    @classmethod
    def symbol(cls) -> str:
        return '\\or'

    @classmethod
    def of(cls: type[Or], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Or:
        cls._check_symbol(symbol)
        (sort,) = sorts
        return Or(sort=sort, ops=patterns)

    @classmethod
    def _from_dict(cls: type[Or], dct: Mapping[str, Any], patterns: list[Pattern]) -> Or:
        return Or(sort=Sort.from_dict(dct['sort']), ops=patterns)


class MLQuant(MLPattern, WithSort):
    sort: Sort
    var: EVar  # TODO Should this be inlined to var_name, var_sort?
    pattern: Pattern

    @property
    def sorts(self) -> tuple[Sort]:
        return (self.sort,)

    @property
    def patterns(self) -> tuple[Pattern]:
        return (self.pattern,)

    @property
    def ctor_patterns(self) -> tuple[EVar, Pattern]:
        return (self.var, self.pattern)

    def _dict(self, dicts: list) -> dict[str, Any]:
        (arg,) = dicts
        return {
            'tag': self._tag(),
            'sort': self.sort.dict,
            'var': self.var.name,
            'varSort': self.var.sort.dict,
            'arg': arg,
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
        sort: Sort | None = None,
        var: EVar | None = None,
        pattern: Pattern | None = None,
    ) -> Exists:
        sort = sort if sort is not None else self.sort
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Exists(sort=sort, var=var, pattern=pattern)

    def let_sort(self, sort: Sort) -> Exists:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Exists:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Exists'

    @classmethod
    def symbol(cls) -> str:
        return '\\exists'

    @classmethod
    def of(cls: type[Exists], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Exists:
        cls._check_symbol(symbol)
        (sort,) = sorts
        var, pattern = patterns
        var = check_type(var, EVar)
        return Exists(sort=sort, var=var, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Exists], dct: Mapping[str, Any], patterns: list[Pattern]) -> Exists:
        (pattern,) = patterns
        return Exists(
            sort=Sort.from_dict(dct['sort']),
            var=EVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=pattern,
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
        sort: Sort | None = None,
        var: EVar | None = None,
        pattern: Pattern | None = None,
    ) -> Forall:
        sort = sort if sort is not None else self.sort
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Forall(sort=sort, var=var, pattern=pattern)

    def let_sort(self, sort: Sort) -> Forall:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Forall:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Forall'

    @classmethod
    def symbol(cls) -> str:
        return '\\forall'

    @classmethod
    def of(cls: type[Forall], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Forall:
        cls._check_symbol(symbol)
        (sort,) = sorts
        var, pattern = patterns
        var = check_type(var, EVar)
        return Forall(sort=sort, var=var, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Forall], dct: Mapping[str, Any], patterns: list[Pattern]) -> Forall:
        (pattern,) = patterns
        return Forall(
            sort=Sort.from_dict(dct['sort']),
            var=EVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=pattern,
        )


class MLFixpoint(MLPattern):
    var: SVar  # TODO Should this be inlined to var_name, var_sort?
    pattern: Pattern

    @property
    def sorts(self) -> tuple[()]:
        return ()

    @property
    def patterns(self) -> tuple[Pattern]:
        return (self.pattern,)

    @property
    def ctor_patterns(self) -> tuple[SVar, Pattern]:
        return (self.var, self.pattern)

    def _dict(self, dicts: list) -> dict[str, Any]:
        (arg,) = dicts
        return {
            'tag': self._tag(),
            'var': self.var.name,
            'varSort': self.var.sort.dict,
            'arg': arg,
        }


@final
@dataclass(frozen=True)
class Mu(MLFixpoint):
    var: SVar
    pattern: Pattern

    def let(self, *, var: SVar | None = None, pattern: Pattern | None = None) -> Mu:
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Mu(var=var, pattern=pattern)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Mu:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Mu'

    @classmethod
    def symbol(cls) -> str:
        return '\\mu'

    @classmethod
    def of(cls: type[Mu], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Mu:
        cls._check_symbol(symbol)
        () = sorts
        var, pattern = patterns
        var = check_type(var, SVar)
        return Mu(var=var, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Mu], dct: Mapping[str, Any], patterns: list[Pattern]) -> Mu:
        (pattern,) = patterns
        return Mu(
            var=SVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=pattern,
        )


@final
@dataclass(frozen=True)
class Nu(MLFixpoint):
    var: SVar
    pattern: Pattern

    def let(self, *, var: SVar | None = None, pattern: Pattern | None = None) -> Nu:
        var = var if var is not None else self.var
        pattern = pattern if pattern is not None else self.pattern
        return Nu(var=var, pattern=pattern)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Nu:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Nu'

    @classmethod
    def symbol(cls) -> str:
        return '\\nu'

    @classmethod
    def of(cls: type[Nu], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Nu:
        cls._check_symbol(symbol)
        () = sorts
        var, pattern = patterns
        var = check_type(var, SVar)
        return Nu(var=var, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Nu], dct: Mapping[str, Any], patterns: list[Pattern]) -> Nu:
        (pattern,) = patterns
        return Nu(
            var=SVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),
            pattern=pattern,
        )


class MLPred(MLPattern, WithSort):
    op_sort: Sort


class RoundPred(MLPred):
    pattern: Pattern

    @property
    def sorts(self) -> tuple[Sort, Sort]:
        return (self.op_sort, self.sort)

    @property
    def patterns(self) -> tuple[Pattern]:
        return (self.pattern,)

    def _dict(self, dicts: list) -> dict[str, Any]:
        (arg,) = dicts
        return {
            'tag': self._tag(),
            'argSort': self.op_sort.dict,
            'sort': self.sort.dict,
            'arg': arg,
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
        op_sort: Sort | None = None,
        sort: Sort | None = None,
        pattern: Pattern | None = None,
    ) -> Ceil:
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Ceil(op_sort=op_sort, sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> Ceil:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Ceil:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Ceil'

    @classmethod
    def symbol(cls) -> str:
        return '\\ceil'

    @classmethod
    def of(cls: type[Ceil], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Ceil:
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        (pattern,) = patterns
        return Ceil(op_sort=op_sort, sort=sort, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Ceil], dct: Mapping[str, Any], patterns: list[Pattern]) -> Ceil:
        (pattern,) = patterns
        return Ceil(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            pattern=pattern,
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
        op_sort: Sort | None = None,
        sort: Sort | None = None,
        pattern: Pattern | None = None,
    ) -> Floor:
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Floor(op_sort=op_sort, sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> Floor:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Floor:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Floor'

    @classmethod
    def symbol(cls) -> str:
        return '\\floor'

    @classmethod
    def of(cls: type[Floor], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Floor:
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        (pattern,) = patterns
        return Floor(op_sort=op_sort, sort=sort, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Floor], dct: Mapping[str, Any], patterns: list[Pattern]) -> Floor:
        (pattern,) = patterns
        return Floor(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            pattern=pattern,
        )


class BinaryPred(MLPred):
    left: Pattern
    right: Pattern

    @property
    def sorts(self) -> tuple[Sort, Sort]:
        return (self.op_sort, self.sort)

    @property
    def patterns(self) -> tuple[Pattern, Pattern]:
        return (self.left, self.right)

    def _dict(self, dicts: list) -> dict[str, Any]:
        first, second = dicts
        return {
            'tag': self._tag(),
            'argSort': self.op_sort.dict,
            'sort': self.sort.dict,
            'first': first,
            'second': second,
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
        op_sort: Sort | None = None,
        sort: Sort | None = None,
        left: Pattern | None = None,
        right: Pattern | None = None,
    ) -> Equals:
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Equals(op_sort=op_sort, sort=sort, left=left, right=right)

    def let_sort(self, sort: Sort) -> Equals:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Equals:
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Equals'

    @classmethod
    def symbol(cls) -> str:
        return '\\equals'

    @classmethod
    def of(cls: type[Equals], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Equals:
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        left, right = patterns
        return Equals(op_sort=op_sort, sort=sort, left=left, right=right)

    @classmethod
    def _from_dict(cls: type[Equals], dct: Mapping[str, Any], patterns: list[Pattern]) -> Equals:
        left, right = patterns
        return Equals(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            left=left,
            right=right,
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
        op_sort: Sort | None = None,
        sort: Sort | None = None,
        left: Pattern | None = None,
        right: Pattern | None = None,
    ) -> In:
        op_sort = op_sort if op_sort is not None else self.op_sort
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return In(op_sort=op_sort, sort=sort, left=left, right=right)

    def let_sort(self, sort: Sort) -> In:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> In:
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'In'

    @classmethod
    def symbol(cls) -> str:
        return '\\in'

    @classmethod
    def of(cls: type[In], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> In:
        cls._check_symbol(symbol)
        op_sort, sort = sorts
        left, right = patterns
        return In(op_sort=op_sort, sort=sort, left=left, right=right)

    @classmethod
    def _from_dict(cls: type[In], dct: Mapping[str, Any], patterns: list[Pattern]) -> In:
        left, right = patterns
        return In(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['sort']),
            left=left,
            right=right,
        )


class MLRewrite(MLPattern, WithSort):
    @property
    def sorts(self) -> tuple[Sort]:
        return (self.sort,)


@final
@dataclass(frozen=True)
class Next(MLRewrite):
    sort: Sort
    pattern: Pattern

    def let(self, *, sort: Sort | None = None, pattern: Pattern | None = None) -> Next:
        sort = sort if sort is not None else self.sort
        pattern = pattern if pattern is not None else self.pattern
        return Next(sort=sort, pattern=pattern)

    def let_sort(self, sort: Sort) -> Next:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Next:
        (pattern,) = patterns
        return self.let(pattern=pattern)

    @classmethod
    def _tag(cls) -> str:
        return 'Next'

    @classmethod
    def symbol(cls) -> str:
        return '\\next'

    @classmethod
    def of(cls: type[Next], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Next:
        cls._check_symbol(symbol)
        (sort,) = sorts
        (pattern,) = patterns
        return Next(sort=sort, pattern=pattern)

    @classmethod
    def _from_dict(cls: type[Next], dct: Mapping[str, Any], patterns: list[Pattern]) -> Next:
        (pattern,) = patterns
        return Next(
            sort=Sort.from_dict(dct['sort']),
            pattern=pattern,
        )

    @property
    def patterns(self) -> tuple[Pattern]:
        return (self.pattern,)

    def _dict(self, dicts: list) -> dict[str, Any]:
        (dest,) = dicts
        return {'tag': 'Next', 'sort': self.sort.dict, 'dest': dest}


@final
@dataclass(frozen=True)
class Rewrites(MLRewrite):
    sort: Sort
    left: Pattern
    right: Pattern

    def let(
        self,
        *,
        sort: Sort | None = None,
        left: Pattern | None = None,
        right: Pattern | None = None,
    ) -> Rewrites:
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        return Rewrites(sort=sort, left=left, right=right)

    def let_sort(self, sort: Sort) -> Rewrites:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> Rewrites:
        left, right = patterns
        return self.let(left=left, right=right)

    @classmethod
    def _tag(cls) -> str:
        return 'Rewrites'

    @classmethod
    def symbol(cls) -> str:
        return '\\rewrites'

    @classmethod
    def of(cls: type[Rewrites], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> Rewrites:
        cls._check_symbol(symbol)
        (sort,) = sorts
        left, right = patterns
        return Rewrites(sort=sort, left=left, right=right)

    @classmethod
    def _from_dict(cls: type[Rewrites], dct: Mapping[str, Any], patterns: list[Pattern]) -> Rewrites:
        left, right = patterns
        return Rewrites(
            sort=Sort.from_dict(dct['sort']),
            left=left,
            right=right,
        )

    @property
    def patterns(self) -> tuple[Pattern, Pattern]:
        return (self.left, self.right)

    def _dict(self, dicts: list) -> dict[str, Any]:
        source, dest = dicts
        return {
            'tag': 'Rewrites',
            'sort': self.sort.dict,
            'source': source,
            'dest': dest,
        }


@final
@dataclass(frozen=True)
class DV(MLPattern, WithSort):
    sort: Sort
    value: String  # TODO Should this be changed to str?

    def let(self, *, sort: Sort | None = None, value: String | None = None) -> DV:
        sort = sort if sort is not None else self.sort
        value = value if value is not None else self.value
        return DV(sort=sort, value=value)

    def let_sort(self, sort: Sort) -> DV:
        return self.let(sort=sort)

    def let_patterns(self, patterns: Iterable[Pattern]) -> DV:
        () = patterns
        return self

    @classmethod
    def _tag(cls) -> str:
        return 'DV'

    @classmethod
    def symbol(cls) -> str:
        return '\\dv'

    @classmethod
    def of(cls: type[DV], symbol: str, sorts: Iterable[Sort] = (), patterns: Iterable[Pattern] = ()) -> DV:
        cls._check_symbol(symbol)
        (sort,) = sorts
        (value,) = patterns
        value = check_type(value, String)
        return DV(sort=sort, value=value)

    @classmethod
    def _from_dict(cls: type[DV], dct: Mapping[str, Any], patterns: list[Pattern]) -> DV:
        assert not patterns
        return DV(
            sort=Sort.from_dict(dct['sort']),
            value=String(dct['value']),
        )

    @property
    def sorts(self) -> tuple[Sort]:
        return (self.sort,)

    @property
    def patterns(self) -> tuple[()]:
        return ()

    @property
    def ctor_patterns(self) -> tuple[String]:
        return (self.value,)

    def _dict(self, dicts: list) -> dict[str, Any]:
        assert not dicts
        return {'tag': 'DV', 'sort': self.sort.dict, 'value': self.value.value}


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
}


class WithAttrs(ABC):
    attrs: tuple[App, ...]

    @abstractmethod
    def let_attrs(self: WA, attrs: Iterable[App]) -> WA: ...

    def map_attrs(self: WA, f: Callable[[tuple[App, ...]], Iterable[App]]) -> WA:
        return self.let_attrs(f(self.attrs))


class Sentence(Kore, WithAttrs): ...


@final
@dataclass(frozen=True)
class Import(Sentence):
    module_name: str
    attrs: tuple[App, ...]

    def __init__(self, module_name: str | Id, attrs: Iterable[App] = ()):
        if isinstance(module_name, str):
            module_name = Id(module_name)

        object.__setattr__(self, 'module_name', module_name.value)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(self, *, module_name: str | Id | None = None, attrs: Iterable[App] | None = None) -> Import:
        module_name = module_name if module_name is not None else self.module_name
        attrs = attrs if attrs is not None else self.attrs
        return Import(module_name=module_name, attrs=attrs)

    def let_attrs(self: Import, attrs: Iterable[App]) -> Import:
        return self.let(attrs=attrs)

    def write(self, output: IO[str]) -> None:
        output.write('import ')
        output.write(self.module_name)
        output.write(' [')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')


@final
@dataclass(frozen=True)
class SortDecl(Sentence):
    name: str
    vars: tuple[SortVar, ...]
    attrs: tuple[App, ...]
    hooked: bool

    def __init__(
        self,
        name: str | Id,
        vars: Iterable[SortVar],
        attrs: Iterable[App] = (),
        *,
        hooked: bool = False,
    ):
        if isinstance(name, str):
            name = Id(name)

        object.__setattr__(self, 'name', name.value)
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    def let(
        self,
        *,
        name: str | Id | None = None,
        vars: Iterable[SortVar] | None = None,
        attrs: Iterable[App] | None = None,
        hooked: bool | None = None,
    ) -> SortDecl:
        name = name if name is not None else self.name
        vars = vars if vars is not None else self.vars
        attrs = attrs if attrs is not None else self.attrs
        hooked = hooked if hooked is not None else self.hooked
        return SortDecl(name=name, vars=vars, attrs=attrs, hooked=hooked)

    def let_attrs(self: SortDecl, attrs: Iterable[App]) -> SortDecl:
        return self.let(attrs=attrs)

    def write(self, output: IO[str]) -> None:
        keyword = 'hooked-sort ' if self.hooked else 'sort '
        output.write(keyword)
        output.write(self.name)
        output.write('{')
        _write_sep_by_comma(self.vars, output)
        output.write('} [')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')


@final
@dataclass(frozen=True)
class Symbol(Kore):
    name: str
    vars: tuple[SortVar, ...]

    def __init__(self, name: str | SymbolId, vars: Iterable[SortVar] = ()):
        if isinstance(name, str):
            name = SymbolId(name)

        object.__setattr__(self, 'name', name.value)
        object.__setattr__(self, 'vars', tuple(vars))

    def let(self, *, name: str | SymbolId | None = None, vars: Iterable[SortVar] | None = None) -> Symbol:
        name = name if name is not None else self.name
        vars = vars if vars is not None else self.vars
        return Symbol(name=name, vars=vars)

    def write(self, output: IO[str]) -> None:
        output.write(self.name)
        output.write('{')
        _write_sep_by_comma(self.vars, output)
        output.write('}')


@final
@dataclass(frozen=True)
class SymbolDecl(Sentence):
    symbol: Symbol
    param_sorts: tuple[Sort, ...]
    sort: Sort
    attrs: tuple[App, ...]
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
        symbol: Symbol | None = None,
        param_sorts: Iterable[Sort] | None = None,
        sort: Sort | None = None,
        attrs: Iterable[App] | None = None,
        hooked: bool | None = None,
    ) -> SymbolDecl:
        symbol = symbol if symbol is not None else self.symbol
        param_sorts = param_sorts if param_sorts is not None else self.param_sorts
        sort = sort if sort is not None else self.sort
        attrs = attrs if attrs is not None else self.attrs
        hooked = hooked if hooked is not None else self.hooked
        return SymbolDecl(symbol=symbol, param_sorts=param_sorts, sort=sort, attrs=attrs, hooked=hooked)

    def let_attrs(self: SymbolDecl, attrs: Iterable[App]) -> SymbolDecl:
        return self.let(attrs=attrs)

    def write(self, output: IO[str]) -> None:
        keyword = 'hooked-symbol ' if self.hooked else 'symbol '
        output.write(keyword)
        self.symbol.write(output)
        output.write('(')
        _write_sep_by_comma(self.param_sorts, output)
        output.write(') : ')
        self.sort.write(output)
        output.write(' [')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')


def _ml_symbol_decls() -> tuple[SymbolDecl, ...]:
    S = SortVar('S')  # noqa: N806
    T = SortVar('T')  # noqa: N806
    return (
        SymbolDecl(Symbol(r'\top', (S,)), (), S),
        SymbolDecl(Symbol(r'\bottom', (S,)), (), S),
        SymbolDecl(Symbol(r'\not', (S,)), (S,), S),
        SymbolDecl(Symbol(r'\and', (S,)), (S, S), S),
        SymbolDecl(Symbol(r'\or', (S,)), (S, S), S),
        SymbolDecl(Symbol(r'\implies', (S,)), (S, S), S),
        SymbolDecl(Symbol(r'\iff', (S,)), (S, S), S),
        SymbolDecl(Symbol(r'\ceil', (S, T)), (S,), T),
        SymbolDecl(Symbol(r'\floor', (S, T)), (S,), T),
        SymbolDecl(Symbol(r'\equals', (S, T)), (S, S), T),
        SymbolDecl(Symbol(r'\in', (S, T)), (S, S), T),
    )


ML_SYMBOL_DECLS: Final = _ml_symbol_decls()


@final
@dataclass(frozen=True)
class AliasDecl(Sentence):
    alias: Symbol
    param_sorts: tuple[Sort, ...]
    sort: Sort
    left: App
    right: Pattern
    attrs: tuple[App, ...]

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
        alias: Symbol | None = None,
        param_sorts: Iterable[Sort] | None = None,
        sort: Sort | None = None,
        left: App | None = None,
        right: Pattern | None = None,
        attrs: Iterable[App] | None = None,
    ) -> AliasDecl:
        alias = alias if alias is not None else self.alias
        param_sorts = param_sorts if param_sorts is not None else self.param_sorts
        sort = sort if sort is not None else self.sort
        left = left if left is not None else self.left
        right = right if right is not None else self.right
        attrs = attrs if attrs is not None else self.attrs
        return AliasDecl(alias=alias, param_sorts=param_sorts, sort=sort, left=left, right=right, attrs=attrs)

    def let_attrs(self: AliasDecl, attrs: Iterable[App]) -> AliasDecl:
        return self.let(attrs=attrs)

    def write(self, output: IO[str]) -> None:
        output.write('alias ')
        self.alias.write(output)
        output.write('(')
        _write_sep_by_comma(self.param_sorts, output)
        output.write(') : ')
        self.sort.write(output)
        output.write(' where ')
        self.left.write(output)
        output.write(' := ')
        self.right.write(output)
        output.write(' [')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')


class AxiomLike(Sentence):
    _label: ClassVar[str]

    vars: tuple[SortVar, ...]
    pattern: Pattern

    def write(self, output: IO[str]) -> None:
        output.write(self._label)
        output.write('{')
        _write_sep_by_comma(self.vars, output)
        output.write('} ')
        self.pattern.write(output)
        output.write(' [')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')


@final
@dataclass(frozen=True)
class Axiom(AxiomLike):
    _label = 'axiom'

    vars: tuple[SortVar, ...]
    pattern: Pattern
    attrs: tuple[App, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[App] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        vars: Iterable[SortVar] | None = None,
        pattern: Pattern | None = None,
        attrs: Iterable[App] | None = None,
    ) -> Axiom:
        vars = vars if vars is not None else self.vars
        pattern = pattern if pattern is not None else self.pattern
        attrs = attrs if attrs is not None else self.attrs
        return Axiom(vars=vars, pattern=pattern, attrs=attrs)

    def let_attrs(self: Axiom, attrs: Iterable[App]) -> Axiom:
        return self.let(attrs=attrs)


@final
@dataclass(frozen=True)
class Claim(AxiomLike):
    _label = 'claim'

    vars: tuple[SortVar, ...]
    pattern: Pattern
    attrs: tuple[App, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[App] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    def let(
        self,
        *,
        vars: Iterable[SortVar] | None = None,
        pattern: Pattern | None = None,
        attrs: Iterable[App] | None = None,
    ) -> Claim:
        vars = vars if vars is not None else self.vars
        pattern = pattern if pattern is not None else self.pattern
        attrs = attrs if attrs is not None else self.attrs
        return Claim(vars=vars, pattern=pattern, attrs=attrs)

    def let_attrs(self: Claim, attrs: Iterable[App]) -> Claim:
        return self.let(attrs=attrs)


@final
@dataclass(frozen=True)
class Module(Kore, WithAttrs, Iterable[Sentence]):
    name: str
    sentences: tuple[Sentence, ...]
    attrs: tuple[App, ...]

    def __init__(self, name: str | Id, sentences: Iterable[Sentence] = (), attrs: Iterable[App] = ()):
        if isinstance(name, str):
            name = Id(name)

        object.__setattr__(self, 'name', name.value)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'attrs', tuple(attrs))

    def __iter__(self) -> Iterator[Sentence]:
        return iter(self.sentences)

    def let(
        self,
        *,
        name: str | Id | None = None,
        sentences: Iterable[Sentence] | None = None,
        attrs: Iterable[App] | None = None,
    ) -> Module:
        name = name if name is not None else self.name
        sentences = sentences if sentences is not None else self.sentences
        attrs = attrs if attrs is not None else self.attrs
        return Module(name=name, sentences=sentences, attrs=attrs)

    def let_attrs(self: Module, attrs: Iterable[App]) -> Module:
        return self.let(attrs=attrs)

    def write(self, output: IO[str]) -> None:
        output.write('module ')
        output.write(self.name)
        for sentence in self.sentences:
            output.write('\n    ')
            sentence.write(output)
        output.write('\nendmodule [')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')

    @cached_property
    def symbol_decls(self) -> tuple[SymbolDecl, ...]:
        return tuple(sentence for sentence in self if type(sentence) is SymbolDecl)

    @cached_property
    def axioms(self) -> tuple[Axiom, ...]:
        return tuple(sentence for sentence in self if type(sentence) is Axiom)


@final
@dataclass(frozen=True)
class Definition(Kore, WithAttrs, Iterable[Module]):
    modules: tuple[Module, ...]
    attrs: tuple[App, ...]

    def __init__(self, modules: Iterable[Module] = (), attrs: Iterable[App] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'attrs', tuple(attrs))

    def __iter__(self) -> Iterator[Module]:
        return iter(self.modules)

    def let(self, *, modules: Iterable[Module] | None = None, attrs: Iterable[App] | None = None) -> Definition:
        modules = modules if modules is not None else self.modules
        attrs = attrs if attrs is not None else self.attrs
        return Definition(modules=modules, attrs=attrs)

    def let_attrs(self: Definition, attrs: Iterable[App]) -> Definition:
        return self.let(attrs=attrs)

    def write(self, output: IO[str]) -> None:
        output.write('[')
        _write_sep_by_comma(self.attrs, output)
        output.write(']')
        for module in self.modules:
            output.write('\n\n')
            module.write(output)

    @cached_property
    def axioms(self) -> tuple[Axiom, ...]:
        return tuple(sent for module in self.modules for sent in module if isinstance(sent, Axiom))

    def get_axiom_by_ordinal(self, ordinal: int) -> Axiom:
        return self.axioms[ordinal]

    def compute_ordinals(self) -> Definition:
        new_modules = []
        rule_ordinal = 0
        for module in self.modules:
            new_sentences: list[Sentence] = []
            for sentence in module.sentences:
                if type(sentence) is Axiom:
                    ordinal_attr = App('ordinal', (), [String(str(rule_ordinal))])
                    new_sentence = sentence.let_attrs(sentence.attrs + (ordinal_attr,))
                    new_sentences.append(new_sentence)
                    rule_ordinal += 1
                else:
                    new_sentences.append(sentence)
            new_modules.append(module.let(sentences=new_sentences))

        new_definition = self.let(modules=new_modules)
        return new_definition


def kore_term(dct: Mapping[str, Any]) -> Pattern:
    if dct['format'] != 'KORE':
        raise ValueError(f"Invalid format: {dct['format']}")

    if dct['version'] != 1:
        raise ValueError(f"Invalid version: {dct['version']}")

    return Pattern.from_dict(dct['term'])
