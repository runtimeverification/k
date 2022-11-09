import json
import logging
from abc import ABC, abstractmethod
from dataclasses import InitVar, dataclass, fields
from enum import Enum
from functools import cached_property, reduce
from itertools import chain
from os import PathLike
from typing import (
    Any,
    Callable,
    ClassVar,
    Dict,
    Final,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
    Type,
    TypeVar,
    Union,
    final,
    overload,
)

from .utils import EMPTY_FROZEN_DICT, FrozenDict, filter_none, hash_str, single

T = TypeVar('T', bound='KAst')
W = TypeVar('W', bound='WithKAtt')
KI = TypeVar('KI', bound='KInner')
RL = TypeVar('RL', bound='KRuleLike')

_LOGGER: Final = logging.getLogger(__name__)


class KAst(ABC):
    @classmethod
    @abstractmethod
    def from_dict(cls: Type[T], d: Dict[str, Any]) -> T:
        node = d['node']
        return globals()[node].from_dict(d)

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


class KInner(KAst):
    _INNER_NODES: Final = {'KVariable', 'KSort', 'KToken', 'KLabel', 'KApply', 'KAs', 'KRewrite', 'KSequence'}

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KInner'], d: Dict[str, Any]) -> 'KInner':
        node = d['node']
        if node in KInner._INNER_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f"Expected KInner label as 'node' value, found: '{node}'")

    @abstractmethod
    def map_inner(self: KI, f: Callable[['KInner'], 'KInner']) -> KI:
        ...

    @abstractmethod
    def match(self, term: 'KInner') -> Optional['Subst']:
        """
        Perform syntactic pattern matching and return the substitution.

        :param term: Term to match.
        :return: Substitution instantiating self to the term.
        """
        ...

    @staticmethod
    def _combine_matches(substs: Iterable[Optional['Subst']]) -> Optional['Subst']:
        def combine(subst1: Optional['Subst'], subst2: Optional['Subst']) -> Optional['Subst']:
            if subst1 is None or subst2 is None:
                return None

            return subst1.union(subst2)

        unit: Optional[Subst] = Subst()
        return reduce(combine, substs, unit)


@dataclass(frozen=True)
class Subst(Mapping[str, KInner]):
    _subst: FrozenDict[str, KInner]

    def __init__(self, subst: Mapping[str, KInner] = EMPTY_FROZEN_DICT):
        object.__setattr__(self, '_subst', FrozenDict(subst))

    def __iter__(self) -> Iterator[str]:
        return iter(self._subst)

    def __len__(self) -> int:
        return len(self._subst)

    def __getitem__(self, key: str) -> KInner:
        return self._subst[key]

    def __mul__(self, other: 'Subst') -> 'Subst':
        return self.compose(other)

    def __call__(self, term: KInner) -> KInner:
        return self.apply(term)

    def minimize(self) -> 'Subst':
        return Subst({k: v for k, v in self.items() if v != KVariable(k)})

    def compose(self, other: 'Subst') -> 'Subst':
        from_other = ((k, self(v)) for k, v in other.items())
        from_self = ((k, v) for k, v in self.items() if k not in other)
        return Subst(dict(chain(from_other, from_self)))

    def union(self, other: 'Subst') -> Optional['Subst']:
        subst = dict(self)
        for v in other:
            if v in subst and subst[v] != other[v]:
                return None
            subst[v] = other[v]
        return Subst(subst)

    def apply(self, term: KInner) -> KInner:
        def replace(term: KInner) -> KInner:
            if type(term) is KVariable and term.name in self:
                return self[term.name]
            return term

        return bottom_up(replace, term)

    def unapply(self, term: KInner) -> KInner:
        new_term = term
        for var_name in self:
            lhs = self[var_name]
            rhs = KVariable(var_name)
            new_term = KRewrite(lhs, rhs).replace(new_term)
        return new_term

    # TODO `kprint: KPrint` introcudes a circular dependency
    def pretty(self, kprint: Any) -> Iterable[str]:
        return (key + ' |-> ' + kprint.pretty_print(value) for key, value in self.items())

    @property
    def ml_pred(self) -> KInner:
        items = []
        for k in self:
            if KVariable(k) != self[k]:
                items.append(KApply('#Equals', [KVariable(k), self[k]]))
        if len(items) == 0:
            return KApply('#Top')
        ml_term = items[0]
        for _i in items[1:]:
            ml_term = KApply('#And', [ml_term, _i])
        return ml_term


@final
@dataclass(frozen=True)
class KSort(KInner):
    name: str

    def __init__(self, name: str):
        object.__setattr__(self, 'name', name)

    @classmethod
    def from_dict(cls: Type['KSort'], d: Dict[str, Any]) -> 'KSort':
        cls._check_node(d)
        return KSort(name=d['name'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KSort', 'name': self.name}

    def let(self, *, name: Optional[str] = None) -> 'KSort':
        name = name if name is not None else self.name
        return KSort(name=name)

    def map_inner(self: 'KSort', f: Callable[[KInner], KInner]) -> 'KSort':
        return self

    def match(self, term: KInner) -> Optional[Subst]:
        raise TypeError('KSort does not support pattern matching')


@final
@dataclass(frozen=True)
class KToken(KInner):
    token: str
    sort: KSort

    def __init__(self, token: str, sort: Union[str, KSort]):
        if type(sort) is str:
            sort = KSort(sort)

        object.__setattr__(self, 'token', token)
        object.__setattr__(self, 'sort', sort)

    @classmethod
    def from_dict(cls: Type['KToken'], d: Dict[str, Any]) -> 'KToken':
        cls._check_node(d)
        return KToken(token=d['token'], sort=KSort.from_dict(d['sort']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KToken', 'token': self.token, 'sort': self.sort.to_dict()}

    def let(self, *, token: Optional[str] = None, sort: Optional[Union[str, KSort]] = None) -> 'KToken':
        token = token if token is not None else self.token
        sort = sort if sort is not None else self.sort
        return KToken(token=token, sort=sort)

    def map_inner(self: 'KToken', f: Callable[[KInner], KInner]) -> 'KToken':
        return self

    def match(self, term: KInner) -> Optional[Subst]:
        if type(term) is KToken:
            return Subst() if term.token == self.token else None
        _LOGGER.debug(f'Matching failed: ({self}.match({term}))')
        return None


@final
@dataclass(frozen=True)
class KVariable(KInner, WithKAtt):
    name: str
    att: KAtt

    def __init__(self, name: str, *, sort: Optional[KSort] = None, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'name', name)
        if sort is not None:
            if KAtt.SORT in att:
                raise ValueError('Both sort and sort attribute provided.')
            att = att.update({KAtt.SORT: sort.to_dict()})
        object.__setattr__(self, 'att', att)

    @property
    def sort(self) -> Optional[KSort]:
        if KAtt.SORT in self.att:
            return KSort.from_dict(self.att[KAtt.SORT])
        return None

    @classmethod
    def from_dict(cls: Type['KVariable'], d: Dict[str, Any]) -> 'KVariable':
        cls._check_node(d)
        return KVariable(
            name=d['name'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KVariable', 'name': self.name, 'att': self.att.to_dict()}

    def let(
        self, *, name: Optional[str] = None, sort: Optional[KSort] = None, att: Optional[KAtt] = None
    ) -> 'KVariable':
        # TODO: We actually want `sort: Optional[Optional['KSort']]`
        name = name if name is not None else self.name
        att = att if att is not None else self.att
        if sort is not None:
            att = att.update({KAtt.SORT: None})
        return KVariable(name=name, sort=sort, att=att)

    def let_att(self, att: KAtt) -> 'KVariable':
        return self.let(att=att)

    def map_inner(self: 'KVariable', f: Callable[[KInner], KInner]) -> 'KVariable':
        return self

    def match(self, term: KInner) -> Subst:
        return Subst({self.name: term})


BOOL: Final = KSort('Bool')
TRUE: Final = KToken('true', BOOL)
FALSE: Final = KToken('false', BOOL)


@final
@dataclass(frozen=True)
class KLabel(KInner):
    name: str
    params: Tuple[KSort, ...]

    @overload
    def __init__(self, name: str, params: Iterable[Union[str, KSort]]):
        ...

    @overload
    def __init__(self, name: str, *params: Union[str, KSort]):
        ...

    # TODO Is it possible to extract a decorator?
    def __init__(self, name: str, *args: Any, **kwargs: Any):
        if kwargs:
            bad_arg = next((arg for arg in kwargs if arg != 'params'), None)
            if bad_arg:
                raise TypeError(f"KLabel() got an unexpected keyword argument '{bad_arg}'")
            if args:
                raise TypeError("KLabel() got multiple values for argument 'params'")
            params = kwargs['params']

        elif len(args) == 1 and isinstance(args[0], Iterable) and not isinstance(args[0], KInner):
            params = args[0]

        else:
            params = args

        params = tuple(KSort(param) if type(param) is str else param for param in params)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'params', params)

    def __iter__(self) -> Iterator[Union[str, KSort]]:
        return chain([self.name], self.params)

    @overload
    def __call__(self, args: Iterable[KInner]) -> 'KApply':
        ...

    @overload
    def __call__(self, *args: KInner) -> 'KApply':
        ...

    def __call__(self, *args: Any, **kwargs: Any) -> 'KApply':
        return self.apply(*args, **kwargs)

    @classmethod
    def from_dict(cls: Type['KLabel'], d: Dict[str, Any]) -> 'KLabel':
        cls._check_node(d)
        return KLabel(name=d['name'], params=(KSort.from_dict(param) for param in d['params']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KLabel', 'name': self.name, 'params': [param.to_dict() for param in self.params]}

    def let(self, *, name: Optional[str] = None, params: Optional[Iterable[Union[str, KSort]]] = None) -> 'KLabel':
        name = name if name is not None else self.name
        params = params if params is not None else self.params
        return KLabel(name=name, params=params)

    def map_inner(self: 'KLabel', f: Callable[[KInner], KInner]) -> 'KLabel':
        return self

    def match(self, term: KInner) -> Optional[Subst]:
        raise TypeError('KLabel does not support pattern matching')

    @overload
    def apply(self, args: Iterable[KInner]) -> 'KApply':
        ...

    @overload
    def apply(self, *args: KInner) -> 'KApply':
        ...

    def apply(self, *args: Any, **kwargs: Any) -> 'KApply':
        return KApply(self, *args, **kwargs)


@final
@dataclass(frozen=True)
class KApply(KInner):
    label: KLabel
    args: Tuple[KInner, ...]

    @overload
    def __init__(self, label: Union[str, KLabel], args: Iterable[KInner]):
        ...

    @overload
    def __init__(self, label: Union[str, KLabel], *args: KInner):
        ...

    def __init__(self, label: Union[str, KLabel], *args: Any, **kwargs: Any):
        if type(label) is str:
            label = KLabel(label)

        if kwargs:
            bad_arg = next((arg for arg in kwargs if arg != 'args'), None)
            if bad_arg:
                raise TypeError(f"KApply() got an unexpected keyword argument '{bad_arg}'")
            if args:
                raise TypeError("KApply() got multiple values for argument 'args'")
            _args = kwargs['args']

        elif len(args) == 1 and isinstance(args[0], Iterable) and not isinstance(args[0], KInner):
            _args = args[0]

        else:
            _args = args

        object.__setattr__(self, 'label', label)
        object.__setattr__(self, 'args', tuple(_args))

    @property
    def arity(self) -> int:
        return len(self.args)

    @property
    def is_cell(self) -> bool:
        return len(self.label.name) > 1 and self.label.name[0] == '<' and self.label.name[-1] == '>'

    @classmethod
    def from_dict(cls: Type['KApply'], d: Dict[str, Any]) -> 'KApply':
        cls._check_node(d)
        return KApply(label=KLabel.from_dict(d['label']), args=(KInner.from_dict(arg) for arg in d['args']))

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KApply',
            'label': self.label.to_dict(),
            'args': [arg.to_dict() for arg in self.args],
            'arity': self.arity,
            'variable': False,
        }

    def let(self, *, label: Optional[Union[str, KLabel]] = None, args: Optional[Iterable[KInner]] = None) -> 'KApply':
        label = label if label is not None else self.label
        args = args if args is not None else self.args
        return KApply(label=label, args=args)

    def map_inner(self: 'KApply', f: Callable[[KInner], KInner]) -> 'KApply':
        return self.let(args=(f(arg) for arg in self.args))

    def match(self, term: KInner) -> Optional[Subst]:
        if type(term) is KApply and term.label.name == self.label.name and term.arity == self.arity:
            return KInner._combine_matches(arg.match(term_arg) for arg, term_arg in zip(self.args, term.args))
        _LOGGER.debug(f'Matching failed: ({self}.match({term}))')
        return None


@final
@dataclass(frozen=True)
class KAs(KInner):
    pattern: KInner
    alias: KInner

    def __init__(self, pattern: KInner, alias: KInner):
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'alias', alias)

    @classmethod
    def from_dict(cls: Type['KAs'], d: Dict[str, Any]) -> 'KAs':
        cls._check_node(d)
        return KAs(pattern=KInner.from_dict(d['pattern']), alias=KInner.from_dict(d['alias']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KAs', 'pattern': self.pattern.to_dict(), 'alias': self.alias.to_dict()}

    def let(
        self, *, pattern: Optional[KInner] = None, alias: Optional[KInner] = None, att: Optional[KAtt] = None
    ) -> 'KAs':
        pattern = pattern if pattern is not None else self.pattern
        alias = alias if alias is not None else self.alias
        return KAs(pattern=pattern, alias=alias)

    def map_inner(self: 'KAs', f: Callable[[KInner], KInner]) -> 'KAs':
        return self.let(pattern=f(self.pattern), alias=f(self.alias))

    def match(self, term: KInner) -> Optional[Subst]:
        raise TypeError('KAs does not support pattern matching')


@final
@dataclass(frozen=True)
class KRewrite(KInner, WithKAtt):
    lhs: KInner
    rhs: KInner

    def __init__(self, lhs: KInner, rhs: KInner, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'lhs', lhs)
        object.__setattr__(self, 'rhs', rhs)
        object.__setattr__(self, 'att', att)

    def __iter__(self) -> Iterator[KInner]:
        return iter([self.lhs, self.rhs])

    def __call__(self, term: KInner, *, top: bool = False) -> KInner:
        if top:
            return self.apply_top(term)

        return self.apply(term)

    @classmethod
    def from_dict(cls: Type['KRewrite'], d: Dict[str, Any]) -> 'KRewrite':
        cls._check_node(d)
        return KRewrite(
            lhs=KInner.from_dict(d['lhs']),
            rhs=KInner.from_dict(d['rhs']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KRewrite',
            'lhs': self.lhs.to_dict(),
            'rhs': self.rhs.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        lhs: Optional[KInner] = None,
        rhs: Optional[KInner] = None,
        att: Optional[KAtt] = None,
    ) -> 'KRewrite':
        lhs = lhs if lhs is not None else self.lhs
        rhs = rhs if rhs is not None else self.rhs
        att = att if att is not None else self.att
        return KRewrite(lhs=lhs, rhs=rhs, att=att)

    def let_att(self, att: KAtt) -> 'KRewrite':
        return self.let(att=att)

    def map_inner(self: 'KRewrite', f: Callable[[KInner], KInner]) -> 'KRewrite':
        return self.let(lhs=f(self.lhs), rhs=f(self.rhs))

    def match(self, term: KInner) -> Optional[Subst]:
        if type(term) is KRewrite:
            lhs_subst = self.lhs.match(term.lhs)
            rhs_subst = self.rhs.match(term.rhs)
            if lhs_subst is None or rhs_subst is None:
                return None
            return lhs_subst.union(rhs_subst)
        _LOGGER.debug(f'Matching failed: ({self}.match({term}))')
        return None

    def apply_top(self, term: KInner) -> KInner:
        """
        Rewrite a given term at the top

        :param term: Term to rewrite.
        :return: The term with the rewrite applied once at the top.
        """
        subst = self.lhs.match(term)
        if subst is not None:
            return subst(self.rhs)
        return term

    def apply(self, term: KInner) -> KInner:
        """
        Attempt rewriting once at every position in a term bottom-up.

        :param term: Term to rewrite.
        :return: The term with rewrites applied at every node once starting from the bottom.
        """
        return bottom_up(self.apply_top, term)

    def replace_top(self, term: KInner) -> KInner:
        if self.lhs == term:
            return self.rhs
        return term

    def replace(self, term: KInner) -> KInner:
        return bottom_up(self.replace_top, term)


@final
@dataclass(frozen=True)
class KSequence(KInner, Sequence[KInner]):
    items: Tuple[KInner, ...]

    @overload
    def __init__(self, items: Iterable[KInner]):
        ...

    @overload
    def __init__(self, *items: KInner):
        ...

    def __init__(self, *args: Any, **kwargs: Any):
        if kwargs:
            bad_arg = next((arg for arg in kwargs if arg != 'items'), None)
            if bad_arg:
                raise TypeError(f"KSequence() got an unexpected keyword argument '{bad_arg}'")
            if args:
                raise TypeError("KSequence() got multiple values for argument 'items'")
            items = kwargs['items']

        elif len(args) == 1 and isinstance(args[0], Iterable) and not isinstance(args[0], KInner):
            items = args[0]

        else:
            items = args

        _items = []
        for i in items:
            if type(i) is KSequence:
                _items.extend(list(i.items))
            else:
                _items.append(i)
        items = tuple(_items)

        object.__setattr__(self, 'items', tuple(items))

    @overload
    def __getitem__(self, key: int) -> KInner:
        ...

    @overload
    def __getitem__(self, key: slice) -> Tuple[KInner, ...]:
        ...

    def __getitem__(self, key: Union[int, slice]) -> Union[KInner, Tuple[KInner, ...]]:
        return self.items[key]

    def __len__(self) -> int:
        return self.arity

    @property
    def arity(self) -> int:
        return len(self.items)

    @classmethod
    def from_dict(cls: Type['KSequence'], d: Dict[str, Any]) -> 'KSequence':
        cls._check_node(d)
        return KSequence(items=(KInner.from_dict(item) for item in d['items']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KSequence', 'items': [item.to_dict() for item in self.items], 'arity': self.arity}

    def let(self, *, items: Optional[Iterable[KInner]] = None) -> 'KSequence':
        items = items if items is not None else self.items
        return KSequence(items=items)

    def map_inner(self: 'KSequence', f: Callable[[KInner], KInner]) -> 'KSequence':
        return self.let(items=(f(item) for item in self.items))

    def match(self, term: KInner) -> Optional[Subst]:
        if type(term) is KSequence:
            if term.arity == self.arity:
                return KInner._combine_matches(item.match(term_item) for item, term_item in zip(self.items, term.items))
            if 0 < self.arity and self.arity < term.arity and type(self.items[-1]) is KVariable:
                common_length = len(self.items) - 1
                _subst: Optional[Subst] = Subst({self.items[-1].name: KSequence(term.items[common_length:])})
                for si, ti in zip(self.items[:common_length], term.items[:common_length]):
                    _subst = KInner._combine_matches([_subst, si.match(ti)])
                return _subst
        _LOGGER.debug(f'Matching failed: ({self}.match({term}))')
        return None


class KOuter(KAst):
    _OUTER_NODES: Final = {
        'KTerminal',
        'KRegexTerminal',
        'KNonTerminal',
        'KProduction',
        'KSyntaxSort',
        'KSortSynonym',
        'KSyntaxLexical',
        'KSyntaxAssociativity',
        'KSyntaxPriority',
        'KBubble',
        'KRule',
        'KClaim',
        'KContext',
        'KImport',
        'KFlatModule',
        'KFlatModuleList',
        'KRequire',
        'KDefinition',
    }

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KOuter'], d: Dict[str, Any]) -> 'KOuter':
        node = d['node']
        if node in KOuter._OUTER_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f"Expected KOuter label as 'node' value, found: '{node}'")


class KProductionItem(KOuter):
    _PRODUCTION_ITEM_NODES: Final = {'KTerminal', 'KRegexTerminal', 'KNonTerminal'}

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KProductionItem'], d: Dict[str, Any]) -> 'KProductionItem':
        node = d['node']
        if node in KProductionItem._PRODUCTION_ITEM_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f"Expected KProductionItem label as 'node' value, found: '{node}'")


class KSentence(KOuter, WithKAtt):
    _SENTENCE_NODES: Final = {
        'KProduction',
        'KSyntaxSort',
        'KSortSynonym',
        'KSyntaxLexical',
        'KSyntaxAssociativity',
        'KSyntaxPriority',
        'KBubble',
        'KRule',
        'KClaim',
        'KContext',
    }

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KSentence'], d: Dict[str, Any]) -> 'KSentence':
        node = d['node']
        if node in KSentence._SENTENCE_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f"Expected KSentence label as 'node' value, found: '{node}'")


@final
@dataclass(frozen=True)
class KTerminal(KProductionItem):
    value: str

    def __init__(self, value: str):
        object.__setattr__(self, 'value', value)

    @classmethod
    def from_dict(cls: Type['KTerminal'], d: Dict[str, Any]) -> 'KTerminal':
        cls._check_node(d)
        return KTerminal(value=d['value'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KTerminal', 'value': self.value}

    def let(self, *, value: Optional[str] = None) -> 'KTerminal':
        value = value if value is not None else self.value
        return KTerminal(value=value)


@final
@dataclass(frozen=True)
class KRegexTerminal(KProductionItem):
    regex: str
    precede_regex: str
    follow_regex: str

    def __init__(self, regex: str, precede_regex: str, follow_regex: str):
        object.__setattr__(self, 'regex', regex)
        object.__setattr__(self, 'precede_regex', precede_regex)
        object.__setattr__(self, 'follow_regex', follow_regex)

    @classmethod
    def from_dict(cls: Type['KRegexTerminal'], d: Dict[str, Any]) -> 'KRegexTerminal':
        cls._check_node(d)
        return KRegexTerminal(
            regex=d['regex'],
            precede_regex=d['precedeRegex'],
            follow_regex=d['followRegex'],
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KRegexTerminal',
            'regex': self.regex,
            'precedeRegex': self.precede_regex,
            'followRegex': self.follow_regex,
        }

    def let(
        self, *, regex: Optional[str] = None, precede_regex: Optional[str] = None, follow_regex: Optional[str] = None
    ) -> 'KRegexTerminal':
        regex = regex if regex is not None else self.regex
        precede_regex = precede_regex if precede_regex is not None else self.precede_regex
        follow_regex = follow_regex if follow_regex is not None else self.follow_regex
        return KRegexTerminal(regex=regex, precede_regex=precede_regex, follow_regex=follow_regex)


@final
@dataclass(frozen=True)
class KNonTerminal(KProductionItem):
    sort: KSort

    def __init__(self, sort: KSort):
        object.__setattr__(self, 'sort', sort)

    @classmethod
    def from_dict(cls: Type['KNonTerminal'], d: Dict[str, Any]) -> 'KNonTerminal':
        cls._check_node(d)
        return KNonTerminal(sort=KSort.from_dict(d['sort']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KNonTerminal', 'sort': self.sort.to_dict()}

    def let(self, *, sort: Optional[KSort] = None) -> 'KNonTerminal':
        sort = sort or self.sort
        return KNonTerminal(sort=sort)


@final
@dataclass(frozen=True)
class KProduction(KSentence):
    # TODO Order in Java implementation: klabel, params, sort, items, att
    sort: KSort
    items: Tuple[KProductionItem, ...]
    params: Tuple[KSort, ...]
    klabel: Optional[KLabel]
    att: KAtt

    def __init__(
        self,
        sort: Union[str, KSort],
        items: Iterable[KProductionItem] = (),
        params: Iterable[Union[str, KSort]] = (),
        klabel: Optional[Union[str, KLabel]] = None,
        att: KAtt = EMPTY_ATT,
    ):
        if type(sort) is str:
            sort = KSort(sort)
        if type(klabel) is str:
            klabel = KLabel(klabel)

        params = tuple(KSort(param) if type(param) is str else param for param in params)

        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'items', tuple(items))
        object.__setattr__(self, 'params', params)
        object.__setattr__(self, 'klabel', klabel)
        object.__setattr__(self, 'att', att)

    @property
    def arity(self) -> int:
        return len(self.items)

    @classmethod
    def from_dict(cls: Type['KProduction'], d: Dict[str, Any]) -> 'KProduction':
        cls._check_node(d)
        return KProduction(
            sort=KSort.from_dict(d['sort']),
            items=(KProductionItem.from_dict(item) for item in d['productionItems']),
            params=(KSort.from_dict(param) for param in d['params']),
            klabel=KLabel.from_dict(d['klabel']) if d.get('klabel') else None,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return filter_none(
            {
                'node': 'KProduction',
                'sort': self.sort.to_dict(),
                'productionItems': [item.to_dict() for item in self.items],
                'params': [param.to_dict() for param in self.params],
                'klabel': self.klabel.to_dict() if self.klabel else None,
                'att': self.att.to_dict(),
            }
        )

    def let(
        self,
        *,
        sort: Optional[Union[str, KSort]] = None,
        items: Optional[Iterable[KProductionItem]] = None,
        params: Optional[Iterable[Union[str, KSort]]] = None,
        klabel: Optional[Union[str, KLabel]] = None,
        att: Optional[KAtt] = None,
    ) -> 'KProduction':
        sort = sort if sort is not None else self.sort
        items = items if items is not None else self.items
        params = params if params is not None else self.params
        klabel = klabel if klabel is not None else self.klabel  # TODO figure out a way to set klabel to None
        att = att if att is not None else self.att
        return KProduction(sort=sort, items=items, params=params, klabel=klabel, att=att)

    def let_att(self, att: KAtt) -> 'KProduction':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSyntaxSort(KSentence):
    sort: KSort
    params: Tuple[KSort, ...]
    att: KAtt

    def __init__(self, sort: KSort, params: Iterable[Union[str, KSort]] = (), att: KAtt = EMPTY_ATT):
        params = tuple(KSort(param) if type(param) is str else param for param in params)
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'params', params)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KSyntaxSort'], d: Dict[str, Any]) -> 'KSyntaxSort':
        cls._check_node(d)
        return KSyntaxSort(
            sort=KSort.from_dict(d['sort']),
            params=(KSort.from_dict(param) for param in d['params']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KSyntaxSort',
            'sort': self.sort.to_dict(),
            'params': [param.to_dict() for param in self.params],
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        sort: Optional[KSort] = None,
        params: Optional[Iterable[Union[str, KSort]]] = None,
        att: Optional[KAtt] = None,
    ) -> 'KSyntaxSort':
        sort = sort or self.sort
        params = params if params is not None else self.params
        att = att if att is not None else self.att
        return KSyntaxSort(sort=sort, params=params, att=att)

    def let_att(self, att: KAtt) -> 'KSyntaxSort':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSortSynonym(KSentence):
    new_sort: KSort
    old_sort: KSort
    att: KAtt

    def __init__(self, new_sort: KSort, old_sort: KSort, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'new_sort', new_sort)
        object.__setattr__(self, 'old_sort', old_sort)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KSortSynonym'], d: Dict[str, Any]) -> 'KSortSynonym':
        cls._check_node(d)
        return KSortSynonym(
            new_sort=KSort.from_dict(d['newSort']),
            old_sort=KSort.from_dict(d['oldSort']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KSortSynonym',
            'newSort': self.new_sort.to_dict(),
            'oldSort': self.old_sort.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(
        self, *, old_sort: Optional[KSort] = None, new_sort: Optional[KSort] = None, att: Optional[KAtt] = None
    ) -> 'KSortSynonym':
        new_sort = new_sort or self.new_sort
        old_sort = old_sort or self.old_sort
        att = att if att is not None else self.att
        return KSortSynonym(new_sort=new_sort, old_sort=old_sort, att=att)

    def let_att(self, att: KAtt) -> 'KSortSynonym':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSyntaxLexical(KSentence):
    name: str
    regex: str
    att: KAtt

    def __init__(self, name: str, regex: str, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'regex', regex)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KSyntaxLexical'], d: Dict[str, Any]) -> 'KSyntaxLexical':
        cls._check_node(d)
        return KSyntaxLexical(
            name=d['name'],
            regex=d['regex'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KSyntaxLexcial',
            'name': self.name,
            'regex': self.regex,
            'att': self.att.to_dict(),
        }

    def let(
        self, *, name: Optional[str] = None, regex: Optional[str] = None, att: Optional[KAtt] = None
    ) -> 'KSyntaxLexical':
        name = name if name is not None else self.name
        regex = regex if regex is not None else self.regex
        att = att if att is not None else self.att
        return KSyntaxLexical(name=name, regex=regex, att=att)

    def let_att(self, att: KAtt) -> 'KSyntaxLexical':
        return self.let(att=att)


class KAssoc(Enum):
    LEFT = 'Left'
    RIGHT = 'Right'
    NON_ASSOC = 'NonAssoc'


@final
@dataclass(frozen=True)
class KSyntaxAssociativity(KSentence):
    assoc: KAssoc
    tags: FrozenSet[str]
    att: KAtt

    def __init__(self, assoc: KAssoc, tags: Iterable[str] = frozenset(), att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'assoc', assoc)
        object.__setattr__(self, 'tags', frozenset(tags))
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KSyntaxAssociativity'], d: Dict[str, Any]) -> 'KSyntaxAssociativity':
        cls._check_node(d)
        return KSyntaxAssociativity(
            assoc=KAssoc(d['assoc']),
            tags=d['tags'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KSyntaxAssociativity',
            'assoc': self.assoc.value,
            'tags': list(self.tags),
            'att': self.att.to_dict(),
        }

    def let(
        self, *, assoc: Optional[KAssoc] = None, tags: Optional[Iterable[str]] = None, att: Optional[KAtt] = None
    ) -> 'KSyntaxAssociativity':
        assoc = assoc or self.assoc
        tags = tags if tags is not None else self.tags
        att = att if att is not None else self.att
        return KSyntaxAssociativity(assoc=assoc, tags=tags, att=att)

    def let_att(self, att: KAtt) -> 'KSyntaxAssociativity':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSyntaxPriority(KSentence):
    priorities: Tuple[FrozenSet[str], ...]
    att: KAtt

    def __init__(self, priorities: Iterable[Iterable[str]] = (), att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'priorities', tuple(frozenset(group) for group in priorities))
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KSyntaxPriority'], d: Dict[str, Any]) -> 'KSyntaxPriority':
        cls._check_node(d)
        return KSyntaxPriority(
            priorities=d['priorities'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KSyntaxPriority',
            'priorities': [list(group) for group in self.priorities],
            'att': self.att.to_dict(),
        }

    def let(
        self, *, priorities: Optional[Iterable[Iterable[str]]] = None, att: Optional[KAtt] = None
    ) -> 'KSyntaxPriority':
        priorities = priorities if priorities is not None else self.priorities
        att = att if att is not None else self.att
        return KSyntaxPriority(priorities=priorities, att=att)

    def let_att(self, att: KAtt) -> 'KSyntaxPriority':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KBubble(KSentence):
    sentence_type: str
    content: str
    att: KAtt

    def __init__(self, sentence_type: str, content: str, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'sentence_type', sentence_type)
        object.__setattr__(self, 'content', content)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KBubble'], d: Dict[str, Any]) -> 'KBubble':
        cls._check_node(d)
        return KBubble(
            sentence_type=d['sentenceType'],
            content=d['content'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KBubble',
            'sentenceType': self.sentence_type,
            'content': self.content,
            'att': self.att.to_dict(),
        }

    def let(
        self, *, sentence_type: Optional[str] = None, content: Optional[str] = None, att: Optional[KAtt] = None
    ) -> 'KBubble':
        sentence_type = sentence_type if sentence_type is not None else self.sentence_type
        content = content if content is not None else self.content
        att = att if att is not None else self.att
        return KBubble(sentence_type=sentence_type, content=content, att=att)

    def let_att(self, att: KAtt) -> 'KBubble':
        return self.let(att=att)


class KRuleLike(KSentence):
    body: KInner
    requires: KInner
    ensures: KInner

    _RULE_LIKE_NODES: Final = {'KRule', 'KClaim'}

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KRuleLike'], d: Dict[str, Any]) -> 'KRuleLike':
        node = d['node']
        if node in KRuleLike._RULE_LIKE_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f"Expected KRuleLike label as 'node' value, found: '{node}'")

    @abstractmethod
    def let(
        self: RL,
        *,
        body: Optional[KInner] = None,
        requires: Optional[KInner] = None,
        ensures: Optional[KInner] = None,
        att: Optional[KAtt] = None,
    ) -> RL:
        ...


@final
@dataclass(frozen=True)
class KRule(KRuleLike):
    body: KInner
    requires: KInner
    ensures: KInner
    att: KAtt

    def __init__(self, body: KInner, requires: KInner = TRUE, ensures: KInner = TRUE, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'body', body)
        object.__setattr__(self, 'requires', requires)
        object.__setattr__(self, 'ensures', ensures)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KRule'], d: Dict[str, Any]) -> 'KRule':
        cls._check_node(d)
        return KRule(
            body=KInner.from_dict(d['body']),
            requires=KInner.from_dict(d['requires']) if d.get('requires') else TRUE,
            ensures=KInner.from_dict(d['ensures']) if d.get('ensures') else TRUE,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KRule',
            'body': self.body.to_dict(),
            'requires': self.requires.to_dict(),
            'ensures': self.ensures.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        body: Optional[KInner] = None,
        requires: Optional[KInner] = None,
        ensures: Optional[KInner] = None,
        att: Optional[KAtt] = None,
    ) -> 'KRule':
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        ensures = ensures if ensures is not None else self.ensures
        att = att if att is not None else self.att
        return KRule(body=body, requires=requires, ensures=ensures, att=att)

    def let_att(self, att: KAtt) -> 'KRule':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KClaim(KRuleLike):
    body: KInner
    requires: KInner
    ensures: KInner
    att: KAtt

    def __init__(self, body: KInner, requires: KInner = TRUE, ensures: KInner = TRUE, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'body', body)
        object.__setattr__(self, 'requires', requires)
        object.__setattr__(self, 'ensures', ensures)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KClaim'], d: Dict[str, Any]) -> 'KClaim':
        cls._check_node(d)
        return KClaim(
            body=KInner.from_dict(d['body']),
            requires=KInner.from_dict(d['requires']) if d.get('requires') else TRUE,
            ensures=KInner.from_dict(d['ensures']) if d.get('ensures') else TRUE,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KClaim',
            'body': self.body.to_dict(),
            'requires': self.requires.to_dict(),
            'ensures': self.ensures.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        body: Optional[KInner] = None,
        requires: Optional[KInner] = None,
        ensures: Optional[KInner] = None,
        att: Optional[KAtt] = None,
    ) -> 'KClaim':
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        ensures = ensures if ensures is not None else self.ensures
        att = att if att is not None else self.att
        return KClaim(body=body, requires=requires, ensures=ensures, att=att)

    def let_att(self, att: KAtt) -> 'KClaim':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KContext(KSentence):
    body: KInner
    requires: KInner
    att: KAtt

    def __init__(self, body: KInner, requires: KInner = TRUE, att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'body', body)
        object.__setattr__(self, 'requires', requires)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KContext'], d: Dict[str, Any]) -> 'KContext':
        cls._check_node(d)
        return KContext(
            body=KInner.from_dict(d['body']),
            requires=KInner.from_dict(d['requires']) if d.get('requires') else TRUE,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KContext',
            'body': self.body.to_dict(),
            'requires': self.requires.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(
        self, *, body: Optional[KInner] = None, requires: Optional[KInner] = None, att: Optional[KAtt] = None
    ) -> 'KContext':
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        att = att if att is not None else self.att
        return KContext(body=body, requires=requires, att=att)

    def let_att(self, att: KAtt) -> 'KContext':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KImport(KOuter):
    name: str
    public: bool

    def __init__(self, name: str, public: bool = True):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'public', public)

    @classmethod
    def from_dict(cls: Type['KImport'], d: Dict[str, Any]) -> 'KImport':
        cls._check_node(d)
        return KImport(name=d['name'], public=d['isPublic'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KImport', 'name': self.name, 'isPublic': self.public}

    def let(self, *, name: Optional[str] = None, public: Optional[bool] = None) -> 'KImport':
        name = name if name is not None else self.name
        public = public if public is not None else self.public
        return KImport(name=name, public=public)


@final
@dataclass(frozen=True)
class KFlatModule(KOuter, WithKAtt):
    name: str
    sentences: Tuple[KSentence, ...]
    imports: Tuple[KImport, ...]
    att: KAtt

    def __init__(
        self, name: str, sentences: Iterable[KSentence] = (), imports: Iterable[KImport] = (), att: KAtt = EMPTY_ATT
    ):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'imports', tuple(imports))
        object.__setattr__(self, 'att', att)

    def __iter__(self) -> Iterator[KSentence]:
        return iter(self.sentences)

    @property
    def productions(self) -> List[KProduction]:
        return [sentence for sentence in self.sentences if type(sentence) is KProduction]

    @property
    def syntax_productions(self) -> List[KProduction]:
        return [prod for prod in self.productions if prod.klabel]

    @property
    def functions(self) -> List[KProduction]:
        def _is_non_free_constructor(label: str) -> bool:
            is_cell_map_constructor = label.endswith('CellMapItem') or label.endswith('CellMap_')
            is_builtin_data_constructor = label in {'_Set_', '_List_', '_Map_', 'SetItem', 'ListItem', '_|->_'}
            return is_cell_map_constructor or is_builtin_data_constructor

        _functions = [
            prod for prod in self.syntax_productions if 'function' in prod.att.atts or 'functional' in prod.att.atts
        ]
        _functions = [f for f in _functions if not (f.klabel and _is_non_free_constructor(f.klabel.name))]
        return _functions

    @property
    def constructors(self) -> List[KProduction]:
        return [prod for prod in self.syntax_productions if prod not in self.functions]

    @property
    def rules(self) -> List[KRule]:
        return [sentence for sentence in self.sentences if type(sentence) is KRule]

    @property
    def claims(self) -> List[KClaim]:
        return [sentence for sentence in self.sentences if type(sentence) is KClaim]

    @classmethod
    def from_dict(cls: Type['KFlatModule'], d: Dict[str, Any]) -> 'KFlatModule':
        cls._check_node(d)
        return KFlatModule(
            name=d['name'],
            sentences=(KSentence.from_dict(sentence) for sentence in d['localSentences']),
            imports=(KImport.from_dict(imp) for imp in d['imports']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KFlatModule',
            'name': self.name,
            'localSentences': [sentence.to_dict() for sentence in self.sentences],
            'imports': [imp.to_dict() for imp in self.imports],
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        name: Optional[str] = None,
        sentences: Optional[Iterable[KSentence]] = None,
        imports: Optional[Iterable[KImport]] = None,
        att: Optional[KAtt] = None,
    ) -> 'KFlatModule':
        name = name if name is not None else self.name
        sentences = sentences if sentences is not None else self.sentences
        imports = imports if imports is not None else self.imports
        att = att if att is not None else self.att
        return KFlatModule(name=name, imports=imports, sentences=sentences, att=att)

    def let_att(self, att: KAtt) -> 'KFlatModule':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KFlatModuleList(KOuter):
    main_module: str
    modules: Tuple[KFlatModule, ...]

    def __init__(self, main_module: str, modules: Iterable[KFlatModule]):
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, 'modules', modules)

    @classmethod
    def from_dict(cls: Type['KFlatModuleList'], d: Dict[str, Any]) -> 'KFlatModuleList':
        cls._check_node(d)
        return KFlatModuleList(main_module=d['mainModule'], modules=(KFlatModule.from_dict(kfm) for kfm in d['term']))

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KFlatModuleList',
            'mainModule': self.main_module,
            'term': [mod.to_dict() for mod in self.modules],
        }

    def let(
        self, *, main_module: Optional[str] = None, modules: Optional[Iterable[KFlatModule]] = None
    ) -> 'KFlatModuleList':
        main_module = main_module if main_module is not None else self.main_module
        modules = modules if modules is not None else self.modules
        return KFlatModuleList(main_module=main_module, modules=modules)


@final
@dataclass(frozen=True)
class KRequire(KOuter):
    require: str

    def __init__(self, require: str):
        object.__setattr__(self, 'require', require)

    @classmethod
    def from_dict(cls: Type['KRequire'], d: Dict[str, Any]) -> 'KRequire':
        cls._check_node(d)
        return KRequire(require=d['require'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KRequire', 'require': self.require}

    def let(self, *, require: Optional[str] = None) -> 'KRequire':
        require = require if require is not None else self.require
        return KRequire(require=require)


@final
@dataclass(frozen=True)
class KDefinition(KOuter, WithKAtt):
    main_module_name: str
    modules: Tuple[KFlatModule, ...]
    requires: Tuple[KRequire, ...]
    att: KAtt

    main_module: InitVar[KFlatModule]

    _production_for_klabel: Dict[KLabel, KProduction]
    _subsorts: Dict[KSort, List[KSort]]

    def __init__(
        self,
        main_module_name: str,
        modules: Iterable[KFlatModule],
        requires: Iterable[KRequire] = (),
        att: KAtt = EMPTY_ATT,
    ):
        modules = tuple(modules)
        main_modules = [module for module in modules if module.name == main_module_name]

        if not main_modules:
            raise ValueError(f"Module '{main_module_name}' not found")
        if len(main_modules) > 1:
            raise ValueError(f"Module '{main_module_name}' is not unique")

        main_module = main_modules[0]

        object.__setattr__(self, 'main_module_name', main_module_name)
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'requires', tuple(requires))
        object.__setattr__(self, 'att', att)
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, '_production_for_klabel', {})
        object.__setattr__(self, '_subsorts', {})

    def __iter__(self) -> Iterator[KFlatModule]:
        return iter(self.modules)

    @classmethod
    def from_dict(cls: Type['KDefinition'], d: Dict[str, Any]) -> 'KDefinition':
        cls._check_node(d)
        return KDefinition(
            main_module_name=d['mainModule'],
            modules=(KFlatModule.from_dict(module) for module in d['modules']),
            requires=(KRequire.from_dict(require) for require in d['requires']) if d.get('requires') else (),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KDefinition',
            'mainModule': self.main_module_name,
            'modules': [module.to_dict() for module in self.modules],
            'requires': [require.to_dict() for require in self.requires],
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        main_module_name: Optional[str] = None,
        modules: Optional[Iterable[KFlatModule]] = None,
        requires: Optional[Iterable[KRequire]] = None,
        att: Optional[KAtt] = None,
    ) -> 'KDefinition':
        main_module_name = main_module_name if main_module_name is not None else self.main_module_name
        modules = modules if modules is not None else self.modules
        requires = requires if requires is not None else self.requires
        att = att if att is not None else self.att
        return KDefinition(main_module_name=main_module_name, modules=modules, requires=requires, att=att)

    def let_att(self, att: KAtt) -> 'KDefinition':
        return self.let(att=att)

    @property
    def module_names(self) -> List[str]:
        return [_m.name for _m in self.modules]

    @property
    def productions(self) -> List[KProduction]:
        return [prod for module in self.modules for prod in module.productions]

    @property
    def syntax_productions(self) -> List[KProduction]:
        return [prod for module in self.modules for prod in module.syntax_productions]

    @property
    def functions(self) -> List[KProduction]:
        return [prod for module in self.modules for prod in module.functions]

    @property
    def constructors(self) -> List[KProduction]:
        return [prod for module in self.modules for prod in module.constructors]

    @property
    def rules(self) -> List[KRule]:
        return [rule for module in self.modules for rule in module.rules]

    def production_for_klabel(self, klabel: KLabel) -> KProduction:
        if klabel not in self._production_for_klabel:
            prods = [prod for prod in self.productions if prod.klabel and prod.klabel.name == klabel.name]
            try:
                self._production_for_klabel[klabel] = single(prods)
            except ValueError as err:
                raise ValueError(f'Expected a single production for label {klabel}, not: {prods}') from err
        return self._production_for_klabel[klabel]

    def production_for_cell_sort(self, sort: KSort) -> KProduction:
        # Typical cell production has 3 productions:
        #     syntax KCell ::= "project:KCell" "(" K ")" [function, projection]
        #     syntax KCell ::= "initKCell" "(" Map ")" [function, initializer, noThread]
        #     syntax KCell ::= "<k>" K "</k>" [cell, cellName(k), format(%1%i%n%2%d%n%3), maincell, org.kframework.definition.Production(syntax #RuleContent ::= #RuleBody [klabel(#ruleNoConditions), symbol])]
        # And it may have a 4th:
        #     syntax GeneratedCounterCell ::= "getGeneratedCounterCell" "(" GeneratedTopCell ")" [function]
        # We want the actual label one (3rd one in the list).
        if not sort.name.endswith('Cell'):
            raise ValueError(
                f'Method production_for_cell_sort only intended to be called on sorts ending in "Cell", not: {sort}'
            )
        try:
            return single(prod for prod in self.productions if prod.sort == sort and 'cell' in prod.att)
        except ValueError as err:
            raise ValueError(f'Expected a single cell production for sort {sort}') from err

    def return_sort(self, label: KLabel) -> KSort:
        return self.production_for_klabel(label).sort

    def argument_sorts(self, label: KLabel) -> List[KSort]:
        return [nt.sort for nt in self.production_for_klabel(label).items if type(nt) is KNonTerminal]

    def subsorts(self, sort: KSort) -> List[KSort]:
        if sort not in self._subsorts:
            self._subsorts[sort] = list(set(self._compute_subsorts(sort)))
        return self._subsorts[sort]

    def _compute_subsorts(self, sort: KSort) -> List[KSort]:
        _subsorts = []
        for prod in self.productions:
            if prod.sort == sort and len(prod.items) == 1 and type(prod.items[0]) is KNonTerminal:
                _subsort = prod.items[0].sort
                _subsorts.extend([_subsort] + self.subsorts(prod.items[0].sort))
        return _subsorts

    def empty_config(self, sort: KSort) -> KInner:
        def _kdefinition_empty_config(_sort: KSort) -> KApply:
            cell_prod = self.production_for_cell_sort(_sort)
            cell_klabel = cell_prod.klabel
            assert cell_klabel is not None
            production = self.production_for_klabel(cell_klabel)
            args: List[KInner] = []
            num_nonterminals = 0
            num_freshvars = 0
            for p_item in production.items:
                if type(p_item) is KNonTerminal:
                    num_nonterminals += 1
                    if p_item.sort.name.endswith('Cell'):
                        args.append(_kdefinition_empty_config(p_item.sort))
                    else:
                        num_freshvars += 1
                        args.append(KVariable(_sort.name[0:-4].upper() + '_CELL'))
            if num_nonterminals > 1 and num_freshvars > 0:
                raise ValueError(f'Found mixed cell and non-cell arguments to cell constructor for: {sort}')
            return KApply(cell_klabel, args)

        return _kdefinition_empty_config(sort)

    def init_config(self, sort: KSort) -> KInner:

        config_var_map = KVariable('__###CONFIG_VAR_MAP###__')

        def _remove_config_var_lookups(_kast: KInner) -> KInner:
            if type(_kast) is KApply and _kast.label.name.startswith('project:') and len(_kast.args) == 1:
                _term = _kast.args[0]
                if type(_term) is KApply and _term.label == KLabel('Map:lookup') and _term.args[0] == config_var_map:
                    _token_var = _term.args[1]
                    if type(_token_var) is KToken and _token_var.sort == KSort('KConfigVar'):
                        return KVariable(_token_var.token)
            return _kast

        init_prods = (prod for prod in self.syntax_productions if 'initializer' in prod.att)
        try:
            init_prod = single(prod for prod in init_prods if prod.sort == sort)
        except ValueError as err:
            raise ValueError(f'Did not find unique initializer for sort: {sort}') from err

        prod_klabel = init_prod.klabel
        assert prod_klabel is not None
        arg_sorts = [nt.sort for nt in init_prod.items if type(nt) is KNonTerminal]
        init_config: KInner
        if len(arg_sorts) == 0:
            init_config = KApply(prod_klabel)
        elif len(arg_sorts) == 1 and arg_sorts[0] == KSort('Map'):
            init_config = KApply(prod_klabel, [config_var_map])
        else:
            raise ValueError(f'Cannot handle initializer for label: {prod_klabel}')

        init_rewrites = [rule.body for rule in self.rules if 'initializer' in rule.att]
        old_init_config: Optional[KInner] = None
        while init_config != old_init_config:
            old_init_config = init_config
            for rew in init_rewrites:
                assert type(rew) is KRewrite
                init_config = rew(init_config)

        init_config = top_down(_remove_config_var_lookups, init_config)

        return init_config


# TODO make method of KInner
def bottom_up(f: Callable[[KInner], KInner], kinner: KInner) -> KInner:
    return f(kinner.map_inner(lambda _kinner: bottom_up(f, _kinner)))


# TODO make method of KInner
def top_down(f: Callable[[KInner], KInner], kinner: KInner) -> KInner:
    return f(kinner).map_inner(lambda _kinner: top_down(f, _kinner))


# TODO replace by method that does not reconstruct the AST
def collect(callback: Callable[[KInner], None], kinner: KInner) -> None:
    def f(kinner: KInner) -> KInner:
        callback(kinner)
        return kinner

    bottom_up(f, kinner)


def build_assoc(unit: KInner, label: Union[str, KLabel], terms: Iterable[KInner]) -> KInner:
    _label = label if type(label) is KLabel else KLabel(label)
    res: Optional[KInner] = None
    for term in reversed(list(terms)):
        if term == unit:
            continue
        if not res:
            res = term
        else:
            res = _label(term, res)
    return res or unit


def build_cons(unit: KInner, label: Union[str, KLabel], terms: Iterable[KInner]) -> KInner:
    it = iter(terms)
    try:
        fst = next(it)
        return KApply(label, (fst, build_cons(unit, label, it)))
    except StopIteration:
        return unit


def read_kast(path: Union[str, PathLike]) -> KAst:
    with open(path, 'r') as _f:
        return KAst.from_dict(json.loads(_f.read())['term'])


def read_kast_definition(path: Union[str, PathLike]) -> KDefinition:
    _defn = read_kast(path)
    assert isinstance(_defn, KDefinition)
    return _defn
