import json
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass, fields
from functools import cached_property
from typing import (
    Any,
    Callable,
    ClassVar,
    Dict,
    Final,
    FrozenSet,
    Iterator,
    Mapping,
    Optional,
    Tuple,
    Type,
    TypeVar,
    final,
)

from ..utils import EMPTY_FROZEN_DICT, FrozenDict, hash_str

T = TypeVar('T', bound='KAst')
W = TypeVar('W', bound='WithKAtt')

_LOGGER: Final = logging.getLogger(__name__)


class KAst(ABC):
    @classmethod
    @abstractmethod
    def from_dict(cls: Type[T], d: Dict[str, Any]) -> T:
        ...

    @abstractmethod
    def to_dict(self) -> Dict[str, Any]:
        ...

    @classmethod
    def from_json(cls: Type[T], s: str) -> T:
        return cls.from_dict(json.loads(s))

    @final
    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True)

    @final
    @cached_property
    def hash(self) -> str:
        return hash_str(self.to_json())

    @classmethod
    def _check_node(cls: Type[T], d: Dict[str, Any], expected: Optional[str] = None) -> None:
        expected = expected if expected is not None else cls.__name__
        actual = d['node']
        if actual != expected:
            raise ValueError(f"Expected '{expected}' as 'node' value, found: '{actual}'")

    def _as_shallow_tuple(self) -> Tuple[Any, ...]:
        # shallow copy version of dataclass.astuple.
        return tuple(self.__dict__[field.name] for field in fields(type(self)))

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, KAst):
            return NotImplemented
        if type(self) == type(other):
            return self._as_shallow_tuple() < other._as_shallow_tuple()
        return type(self).__name__ < type(other).__name__


@final
@dataclass(frozen=True)
class KAtt(KAst, Mapping[str, Any]):
    atts: FrozenDict[str, Any]

    SORT: ClassVar[str] = 'org.kframework.kore.Sort'

    def __init__(self, atts: Mapping[str, Any] = EMPTY_FROZEN_DICT):
        def _freeze(m: Any) -> Any:
            if isinstance(m, (int, str, tuple, FrozenDict, FrozenSet)):
                return m
            elif isinstance(m, list):
                return tuple((v for v in m))
            elif isinstance(m, dict):
                return FrozenDict(((k, _freeze(v)) for (k, v) in m.items()))
            raise ValueError(f"Don't know how to freeze attribute value {m} of type {type(m)}.")

        frozen = _freeze(atts)
        assert isinstance(frozen, FrozenDict)
        object.__setattr__(self, 'atts', frozen)

    def __iter__(self) -> Iterator[str]:
        return iter(self.atts)

    def __len__(self) -> int:
        return len(self.atts)

    def __getitem__(self, key: str) -> Any:
        return self.atts[key]

    @staticmethod
    def of(**atts: Any) -> 'KAtt':
        return KAtt(atts=atts)

    @classmethod
    def from_dict(cls: Type['KAtt'], d: Dict[str, Any]) -> 'KAtt':
        cls._check_node(d)
        return KAtt(atts=d['att'])

    def to_dict(self) -> Dict[str, Any]:
        def _to_dict(m: Any) -> Any:
            if isinstance(m, FrozenDict):
                return {k: _to_dict(v) for (k, v) in m.items()}
            return m

        return {'node': 'KAtt', 'att': _to_dict(self.atts)}

    def let(self, *, atts: Optional[Mapping[str, Any]] = None) -> 'KAtt':
        atts = atts if atts is not None else self.atts
        return KAtt(atts=atts)

    def update(self, atts: Mapping[str, Any]) -> 'KAtt':
        return self.let(atts={k: v for k, v in {**self.atts, **atts}.items() if v is not None})


EMPTY_ATT: Final = KAtt()


class WithKAtt(ABC):
    att: KAtt

    @abstractmethod
    def let_att(self: W, att: KAtt) -> W:
        ...

    def map_att(self: W, f: Callable[[KAtt], KAtt]) -> W:
        return self.let_att(att=f(self.att))

    def update_atts(self: W, atts: Mapping[str, Any]) -> W:
        return self.let_att(att=self.att.update(atts))
