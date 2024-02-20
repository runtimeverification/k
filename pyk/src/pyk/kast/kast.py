from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass, field, fields
from functools import cache, cached_property
from itertools import chain
from pathlib import Path
from typing import TYPE_CHECKING, Any, Generic, Literal, TypeVar, final, overload

from ..utils import FrozenDict, hash_str

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator
    from typing import Final

    U = TypeVar('U')
    W = TypeVar('W', bound='WithKAtt')


T = TypeVar('T')
_LOGGER: Final = logging.getLogger(__name__)


class KAst(ABC):
    @staticmethod
    def version() -> int:
        return 3

    @abstractmethod
    def to_dict(self) -> dict[str, Any]:
        ...

    @final
    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True)

    @final
    @cached_property
    def hash(self) -> str:
        return hash_str(self.to_json())

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, KAst):
            return NotImplemented
        if type(self) == type(other):
            return self._as_shallow_tuple() < other._as_shallow_tuple()
        return type(self).__name__ < type(other).__name__

    def _as_shallow_tuple(self) -> tuple[Any, ...]:
        # shallow copy version of dataclass.astuple.
        return tuple(self.__dict__[field.name] for field in fields(type(self)))  # type: ignore


class AttType(Generic[T], ABC):
    @abstractmethod
    def from_dict(self, obj: Any) -> T:
        ...

    @abstractmethod
    def to_dict(self, value: T) -> Any:
        ...

    @abstractmethod
    def pretty(self, value: T) -> str | None:
        ...


class NullaryType(AttType[Literal['']]):
    def from_dict(self, obj: Any) -> Literal['']:
        assert obj == ''
        return obj

    def to_dict(self, value: Literal['']) -> Any:
        assert value == ''
        return value

    def pretty(self, value: Literal['']) -> None:
        return None


class AnyType(AttType[Any]):
    def from_dict(self, obj: Any) -> Any:
        return self._freeze(obj)

    def to_dict(self, value: Any) -> Any:
        return self._unfreeze(value)

    def pretty(self, value: Any) -> str:
        return str(value)

    @staticmethod
    def _freeze(obj: Any) -> Any:
        if isinstance(obj, list):
            return tuple(AnyType._freeze(v) for v in obj)
        if isinstance(obj, dict):
            return FrozenDict((k, AnyType._freeze(v)) for (k, v) in obj.items())
        return obj

    @staticmethod
    def _unfreeze(value: Any) -> Any:
        if isinstance(value, FrozenDict):
            return {k: AnyType._unfreeze(v) for (k, v) in value.items()}
        return value


class LocationType(AttType[tuple[int, int, int, int]]):
    def from_dict(self, obj: Any) -> tuple[int, int, int, int]:
        assert isinstance(obj, list)
        a, b, c, d = obj
        assert isinstance(a, int)
        assert isinstance(b, int)
        assert isinstance(c, int)
        assert isinstance(d, int)
        return a, b, c, d

    def to_dict(self, value: tuple[int, int, int, int]) -> Any:
        return list(value)

    def pretty(self, value: tuple[int, int, int, int]) -> str:
        return ','.join(str(e) for e in value)


class PathType(AttType[Path]):
    def from_dict(self, obj: Any) -> Path:
        assert isinstance(obj, str)
        return Path(obj)

    def to_dict(self, value: Path) -> Any:
        return str(value)

    def pretty(self, value: Path) -> str:
        return f'"{value}"'


_NULLARY: Final = NullaryType()
_ANY: Final = AnyType()
_LOCATION: Final = LocationType()
_PATH: Final = PathType()


@final
@dataclass(frozen=True)
class AttKey(Generic[T]):
    name: str
    type: AttType[T] = field(compare=False, repr=False, kw_only=True)

    def __call__(self, value: T) -> AttEntry[T]:
        return AttEntry(self, value)


@final
@dataclass(frozen=True)
class AttEntry(Generic[T]):
    key: AttKey[T]
    value: T


class Atts:
    ALIAS: Final = AttKey('alias', type=_NULLARY)
    ALIAS_REC: Final = AttKey('alias-rec', type=_NULLARY)
    ANYWHERE: Final = AttKey('anywhere', type=_NULLARY)
    ASSOC: Final = AttKey('assoc', type=_NULLARY)
    CIRCULARITY: Final = AttKey('circularity', type=_NULLARY)
    CELL: Final = AttKey('cell', type=_NULLARY)
    CELL_COLLECTION: Final = AttKey('cellCollection', type=_NULLARY)
    COLORS: Final = AttKey('colors', type=_ANY)
    COMM: Final = AttKey('comm', type=_NULLARY)
    CONCAT: Final = AttKey('concat', type=_ANY)
    CONSTRUCTOR: Final = AttKey('constructor', type=_NULLARY)
    DEPENDS: Final = AttKey('depends', type=_ANY)
    DIGEST: Final = AttKey('digest', type=_ANY)
    ELEMENT: Final = AttKey('element', type=_ANY)
    FORMAT: Final = AttKey('format', type=_ANY)
    FUNCTION: Final = AttKey('function', type=_NULLARY)
    FUNCTIONAL: Final = AttKey('functional', type=_NULLARY)
    HAS_DOMAIN_VALUES: Final = AttKey('hasDomainValues', type=_NULLARY)
    HOOK: Final = AttKey('hook', type=_ANY)
    IDEM: Final = AttKey('idem', type=_NULLARY)
    INITIALIZER: Final = AttKey('initializer', type=_NULLARY)
    INJECTIVE: Final = AttKey('injective', type=_NULLARY)
    KLABEL: Final = AttKey('klabel', type=_ANY)
    LABEL: Final = AttKey('label', type=_ANY)
    LEFT: Final = AttKey('left', type=_NULLARY)
    LOCATION: Final = AttKey('org.kframework.attributes.Location', type=_LOCATION)
    MACRO: Final = AttKey('macro', type=_NULLARY)
    MACRO_REC: Final = AttKey('macro-rec', type=_NULLARY)
    OWISE: Final = AttKey('owise', type=_NULLARY)
    PRIORITY: Final = AttKey('priority', type=_ANY)
    PRODUCTION: Final = AttKey('org.kframework.definition.Production', type=_ANY)
    PROJECTION: Final = AttKey('projection', type=_NULLARY)
    RIGHT: Final = AttKey('right', type=_NULLARY)
    SIMPLIFICATION: Final = AttKey('simplification', type=_ANY)
    SYMBOL: Final = AttKey('symbol', type=_ANY)
    SORT: Final = AttKey('org.kframework.kore.Sort', type=_ANY)
    SOURCE: Final = AttKey('org.kframework.attributes.Source', type=_PATH)
    TOKEN: Final = AttKey('token', type=_NULLARY)
    TOTAL: Final = AttKey('total', type=_NULLARY)
    TRUSTED: Final = AttKey('trusted', type=_NULLARY)
    UNIT: Final = AttKey('unit', type=_ANY)
    UNIQUE_ID: Final = AttKey('UNIQUE_ID', type=_ANY)
    UNPARSE_AVOID: Final = AttKey('unparseAvoid', type=_NULLARY)
    WRAP_ELEMENT: Final = AttKey('wrapElement', type=_ANY)

    @classmethod
    @cache
    def keys(cls) -> FrozenDict[str, AttKey]:
        keys = [value for value in vars(cls).values() if isinstance(value, AttKey)]
        res: FrozenDict[str, AttKey] = FrozenDict({key.name: key for key in keys})
        assert len(res) == len(keys)  # Fails on duplicate key name
        return res


@final
@dataclass(frozen=True)
class KAtt(KAst, Mapping[AttKey, Any]):
    atts: FrozenDict[AttKey, Any]

    def __init__(self, entries: Iterable[AttEntry] = ()):
        atts: FrozenDict[AttKey, Any] = FrozenDict((e.key, e.value) for e in entries)
        object.__setattr__(self, 'atts', atts)

    def __iter__(self) -> Iterator[AttKey]:
        return iter(self.atts)

    def __len__(self) -> int:
        return len(self.atts)

    def __getitem__(self, key: AttKey[T]) -> T:
        return self.atts[key]

    @overload
    def get(self, key: AttKey[T], /) -> T | None:
        ...

    @overload
    def get(self, key: AttKey[T], /, default: U) -> T | U:
        ...

    def get(self, *args: Any, **kwargs: Any) -> Any:
        return self.atts.get(*args, **kwargs)

    def entries(self) -> Iterator[AttEntry]:
        return (key(value) for key, value in self.atts.items())

    @classmethod
    def from_dict(cls: type[KAtt], d: Mapping[str, Any]) -> KAtt:
        entries: list[AttEntry] = []
        for k, v in d['att'].items():
            key = Atts.keys().get(k, AttKey(k, type=_ANY))
            value = key.type.from_dict(v)
            entries.append(key(value))
        return KAtt(entries=entries)

    def to_dict(self) -> dict[str, Any]:
        return {'node': 'KAtt', 'att': {key.name: key.type.to_dict(value) for key, value in self.atts.items()}}

    @property
    def pretty(self) -> str:
        if not self:
            return ''
        att_strs: list[str] = []
        for key, value in self.items():
            value_str = key.type.pretty(value)
            if value_str is None:
                att_strs.append(key.name)
            else:
                att_strs.append(f'{key.name}({value_str})')
        return f'[{", ".join(att_strs)}]'

    def update(self, entries: Iterable[AttEntry]) -> KAtt:
        entries = chain((AttEntry(key, value) for key, value in self.atts.items()), entries)
        return KAtt(entries=entries)

    def discard(self, keys: Iterable[AttKey]) -> KAtt:
        entries = (AttEntry(key, value) for key, value in self.atts.items() if key not in keys)
        return KAtt(entries=entries)

    def drop_source(self) -> KAtt:
        return self.discard([Atts.SOURCE, Atts.LOCATION])


EMPTY_ATT: Final = KAtt()


class WithKAtt(ABC):
    att: KAtt

    @abstractmethod
    def let_att(self: W, att: KAtt) -> W:
        ...

    def map_att(self: W, f: Callable[[KAtt], KAtt]) -> W:
        return self.let_att(att=f(self.att))

    def update_atts(self: W, entries: Iterable[AttEntry]) -> W:
        return self.let_att(att=self.att.update(entries))


def kast_term(dct: Mapping[str, Any]) -> Mapping[str, Any]:
    if dct['format'] != 'KAST':
        raise ValueError(f"Invalid format: {dct['format']}")

    if dct['version'] != KAst.version():
        raise ValueError(f"Invalid version: {dct['version']}")

    return dct['term']
