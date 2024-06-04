from __future__ import annotations

import logging
import re
from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass, field
from functools import cache
from itertools import chain
from pathlib import Path
from typing import ClassVar  # noqa: TC003
from typing import TYPE_CHECKING, Any, Generic, TypeVar, final, overload

from ..utils import FrozenDict
from .color import Color
from .kast import KAst

if TYPE_CHECKING:
    from collections.abc import Callable, Container, Iterable, Iterator
    from typing import Final

    U = TypeVar('U')
    W = TypeVar('W', bound='WithKAtt')


T = TypeVar('T')
_LOGGER: Final = logging.getLogger(__name__)


class AttType(Generic[T], ABC):
    @abstractmethod
    def from_dict(self, obj: Any) -> T: ...

    @abstractmethod
    def to_dict(self, value: T) -> Any: ...

    @abstractmethod
    def unparse(self, value: T) -> str | None: ...

    @abstractmethod
    def parse(self, text: str) -> T: ...


class NoneType(AttType[None]):
    def from_dict(self, obj: Any) -> None:
        assert obj == ''
        return None

    def to_dict(self, value: None) -> Any:
        assert value is None
        return ''

    def unparse(self, value: None) -> None:
        return None

    def parse(self, text: str) -> None:
        assert text == ''
        return None


class OptionalType(Generic[T], AttType[T | None]):
    _value_type: AttType[T]

    def __init__(self, value_type: AttType[T]):
        self._value_type = value_type

    def from_dict(self, obj: Any) -> T | None:
        if obj == '':
            return None
        return self._value_type.from_dict(obj)

    def to_dict(self, value: T | None) -> Any:
        if value is None:
            return ''
        return self._value_type.to_dict(value)

    def unparse(self, value: T | None) -> str | None:
        if value is None:
            return None
        return self._value_type.unparse(value)

    def parse(self, text: str) -> T | None:
        if text == '':
            return None
        return self._value_type.parse(text)


class AnyType(AttType[Any]):
    def from_dict(self, obj: Any) -> Any:
        return self._freeze(obj)

    def to_dict(self, value: Any) -> Any:
        return self._unfreeze(value)

    def unparse(self, value: Any) -> str:
        return str(value)

    def parse(self, text: str) -> Any:
        raise ValueError(f'Parsing a string into an Any attribute type is not supported. Attempted to parse: {text!r}')

    @staticmethod
    def _freeze(obj: Any) -> Any:
        if isinstance(obj, list):
            return tuple(AnyType._freeze(v) for v in obj)
        if isinstance(obj, dict):
            return FrozenDict((k, AnyType._freeze(v)) for (k, v) in obj.items())
        return obj

    @staticmethod
    def _unfreeze(value: Any) -> Any:
        if isinstance(value, tuple):
            return [AnyType._unfreeze(v) for v in value]
        if isinstance(value, FrozenDict):
            return {k: AnyType._unfreeze(v) for (k, v) in value.items()}
        return value


class IntType(AttType[int]):
    def from_dict(self, obj: Any) -> int:
        assert isinstance(obj, str)
        return int(obj)

    def to_dict(self, value: int) -> str:
        return str(value)

    def unparse(self, value: int) -> str:
        return str(value)

    def parse(self, text: str) -> int:
        return int(text)


class StrType(AttType[str]):
    def from_dict(self, obj: Any) -> str:
        assert isinstance(obj, str)
        return obj

    def to_dict(self, value: str) -> Any:
        return value

    def unparse(self, value: str) -> str:
        return f'"{value}"'

    def parse(self, text: str) -> str:
        return text


class LocationType(AttType[tuple[int, int, int, int]]):
    _PARSE_REGEX: Final = re.compile('(\\d+),(\\d+),(\\d+),(\\d+)')

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

    def unparse(self, value: tuple[int, int, int, int]) -> str:
        return ','.join(str(e) for e in value)

    def parse(self, text: str) -> tuple[int, int, int, int]:
        m = self._PARSE_REGEX.fullmatch(text)
        assert m is not None
        a, b, c, d = (int(x) for x in m.groups())
        return a, b, c, d


class PathType(AttType[Path]):
    def from_dict(self, obj: Any) -> Path:
        assert isinstance(obj, str)
        return Path(obj)

    def to_dict(self, value: Path) -> Any:
        return str(value)

    def unparse(self, value: Path) -> str:
        return f'"{value}"'

    def parse(self, text: str) -> Path:
        return Path(text)


@final
@dataclass(frozen=True)
class Format:
    tokens: tuple[str, ...]

    _pattern: ClassVar[re.Pattern] = re.compile(r'%\D|%\d+|[^%]+')

    def __init__(self, tokens: Iterable[str] = ()):
        object.__setattr__(self, 'tokens', tuple(tokens))

    @classmethod
    def parse(cls, s: str) -> Format:
        matches = list(cls._pattern.finditer(s))

        matched_len: int
        if not matches:
            matched_len = 0
        else:
            _, matched_len = matches[-1].span()

        if matched_len != len(s):
            assert s and s[-1] == '%'
            raise ValueError(f'Incomplete escape sequence at the end of format string: {s}')

        return Format(m[0] for m in matches)

    def unparse(self) -> str:
        return ''.join(self.tokens)


class FormatType(AttType[Format]):
    def from_dict(self, obj: Any) -> Format:
        assert isinstance(obj, str)
        return Format.parse(obj)

    def to_dict(self, value: Format) -> Any:
        return value.unparse()

    def unparse(self, value: Format) -> str:
        return f'"{value.unparse}"'

    def parse(self, text: str) -> Format:
        return Format.parse(text)


class ColorType(AttType[Color]):
    def from_dict(self, obj: Any) -> Color:
        assert isinstance(obj, str)
        return Color(obj)

    def to_dict(self, value: Color) -> str:
        return value.value

    def unparse(self, value: Color) -> str:
        return value.value

    def parse(self, text: str) -> Color:
        return Color(text)


class ColorsType(AttType[tuple[Color, ...]]):
    def from_dict(self, obj: Any) -> tuple[Color, ...]:
        assert isinstance(obj, str)
        return self.parse(obj)

    def to_dict(self, value: tuple[Color, ...]) -> str:
        return self.unparse(value)

    def unparse(self, value: tuple[Color, ...]) -> str:
        return ','.join(v.value for v in value)

    def parse(self, text: str) -> tuple[Color, ...]:
        return tuple(Color(color) for color in text.replace(' ', '').split(','))


_NONE: Final = NoneType()
_ANY: Final = AnyType()
_INT: Final = IntType()
_STR: Final = StrType()
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
    ALIAS: Final = AttKey('alias', type=_NONE)
    ALIAS_REC: Final = AttKey('alias-rec', type=_NONE)
    ANYWHERE: Final = AttKey('anywhere', type=_NONE)
    ASSOC: Final = AttKey('assoc', type=_NONE)
    BRACKET: Final = AttKey('bracket', type=_NONE)
    BRACKET_LABEL: Final = AttKey('bracketLabel', type=_ANY)
    CIRCULARITY: Final = AttKey('circularity', type=_NONE)
    CELL: Final = AttKey('cell', type=_NONE)
    CELL_COLLECTION: Final = AttKey('cellCollection', type=_NONE)
    CELL_FRAGMENT: Final = AttKey('cellFragment', type=_ANY)
    CELL_NAME: Final = AttKey('cellName', type=_STR)
    CELL_OPT_ABSENT: Final = AttKey('cellOptAbsent', type=_ANY)
    COLOR: Final = AttKey('color', type=ColorType())
    COLORS: Final = AttKey('colors', type=ColorsType())
    COMM: Final = AttKey('comm', type=_NONE)
    CONCAT: Final = AttKey('concat', type=_ANY)
    CONCRETE: Final = AttKey('concrete', type=OptionalType(_STR))
    CONSTRUCTOR: Final = AttKey('constructor', type=_NONE)
    DEPENDS: Final = AttKey('depends', type=_ANY)
    DIGEST: Final = AttKey('digest', type=_ANY)
    ELEMENT: Final = AttKey('element', type=_ANY)
    FORMAT: Final = AttKey('format', type=FormatType())
    FRESH_GENERATOR: Final = AttKey('freshGenerator', type=_NONE)
    FUNCTION: Final = AttKey('function', type=_NONE)
    FUNCTIONAL: Final = AttKey('functional', type=_NONE)
    GROUP: Final = AttKey('group', type=_STR)
    HAS_DOMAIN_VALUES: Final = AttKey('hasDomainValues', type=_NONE)
    HOOK: Final = AttKey('hook', type=_ANY)
    IDEM: Final = AttKey('idem', type=_NONE)
    IMPURE: Final = AttKey('impure', type=_NONE)
    INDEX: Final = AttKey('index', type=_INT)
    INITIALIZER: Final = AttKey('initializer', type=_NONE)
    INJECTIVE: Final = AttKey('injective', type=_NONE)
    KLABEL: Final = AttKey('klabel', type=_ANY)
    LABEL: Final = AttKey('label', type=_ANY)
    LEFT: Final = AttKey('left', type=_ANY)  # LEFT and LEFT_INTERNAL on the Frontend
    LOCATION: Final = AttKey('org.kframework.attributes.Location', type=_LOCATION)
    MACRO: Final = AttKey('macro', type=_NONE)
    MACRO_REC: Final = AttKey('macro-rec', type=_NONE)
    MAINCELL: Final = AttKey('maincell', type=_NONE)
    OVERLOAD: Final = AttKey('overload', type=_STR)
    OWISE: Final = AttKey('owise', type=_NONE)
    PREDICATE: Final = AttKey('predicate', type=_ANY)
    PREFER: Final = AttKey('prefer', type=_NONE)
    PRIORITY: Final = AttKey('priority', type=_ANY)
    PRIORITIES: Final = AttKey('priorities', type=_ANY)  # only in KORE output
    PRIVATE: Final = AttKey('private', type=_NONE)
    PRODUCTION: Final = AttKey('org.kframework.definition.Production', type=_ANY)
    PROJECTION: Final = AttKey('projection', type=_NONE)
    RIGHT: Final = AttKey('right', type=_ANY)  # RIGHT and RIGHT_INTERNAL on the Frontend
    SIMPLIFICATION: Final = AttKey('simplification', type=_ANY)
    SEQSTRICT: Final = AttKey('seqstrict', type=_NONE)
    SORT: Final = AttKey('org.kframework.kore.Sort', type=_ANY)
    SOURCE: Final = AttKey('org.kframework.attributes.Source', type=_PATH)
    STRICT: Final = AttKey('strict', type=_ANY)
    SYMBOL: Final = AttKey('symbol', type=OptionalType(_STR))
    SYNTAX_MODULE: Final = AttKey('syntaxModule', type=_STR)
    TERMINALS: Final = AttKey('terminals', type=_STR)
    TOKEN: Final = AttKey('token', type=_NONE)
    TOTAL: Final = AttKey('total', type=_NONE)
    TRUSTED: Final = AttKey('trusted', type=_NONE)
    UNIT: Final = AttKey('unit', type=_STR)
    UNIQUE_ID: Final = AttKey('UNIQUE_ID', type=_ANY)
    UNPARSE_AVOID: Final = AttKey('unparseAvoid', type=_NONE)
    USER_LIST: Final = AttKey('userList', type=_ANY)
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
    def get(self, key: AttKey[T], /) -> T | None: ...

    @overload
    def get(self, key: AttKey[T], /, default: U) -> T | U: ...

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

    @classmethod
    def parse(cls: type[KAtt], d: Mapping[str, str]) -> KAtt:
        entries: list[AttEntry] = []
        for k, v in d.items():
            key = Atts.keys().get(k, AttKey(k, type=_ANY))
            value = key.type.parse(v)
            entries.append(key(value))
        return KAtt(entries=entries)

    @property
    def pretty(self) -> str:
        if not self:
            return ''
        att_strs: list[str] = []
        for key, value in self.items():
            value_str = key.type.unparse(value)
            if value_str is None:
                att_strs.append(key.name)
            else:
                att_strs.append(f'{key.name}({value_str})')
        return f'[{", ".join(att_strs)}]'

    def update(self, entries: Iterable[AttEntry]) -> KAtt:
        entries = chain((AttEntry(key, value) for key, value in self.atts.items()), entries)
        return KAtt(entries=entries)

    def discard(self, keys: Container[AttKey]) -> KAtt:
        entries = (AttEntry(key, value) for key, value in self.atts.items() if key not in keys)
        return KAtt(entries=entries)

    def drop_source(self) -> KAtt:
        return self.discard([Atts.SOURCE, Atts.LOCATION])


EMPTY_ATT: Final = KAtt()


class WithKAtt(ABC):
    att: KAtt

    @abstractmethod
    def let_att(self: W, att: KAtt) -> W: ...

    def map_att(self: W, f: Callable[[KAtt], KAtt]) -> W:
        return self.let_att(att=f(self.att))

    def update_atts(self: W, entries: Iterable[AttEntry]) -> W:
        return self.let_att(att=self.att.update(entries))
