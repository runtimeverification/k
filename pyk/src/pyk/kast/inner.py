import logging
from abc import abstractmethod
from dataclasses import dataclass
from functools import reduce
from itertools import chain
from typing import (
    Any,
    Callable,
    Dict,
    Final,
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

from ..utils import EMPTY_FROZEN_DICT, FrozenDict, dequote_str, enquote_str
from .kast import EMPTY_ATT, KAst, KAtt, WithKAtt

T = TypeVar('T', bound='KAst')
W = TypeVar('W', bound='WithKAtt')
KI = TypeVar('KI', bound='KInner')

_LOGGER: Final = logging.getLogger(__name__)


class KInner(KAst):
    _INNER_NODES: Final = {'KVariable', 'KSort', 'KToken', 'KLabel', 'KApply', 'KAs', 'KRewrite', 'KSequence'}

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KInner'], d: Dict[str, Any]) -> 'KInner':
        node = d['node']
        if node in KInner._INNER_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected KInner label as "node" value, found: {node}')

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

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> 'Subst':
        return Subst({k: KInner.from_dict(v) for k, v in d.items()})

    def to_dict(self) -> Dict[str, Any]:
        return {k: v.to_dict() for k, v in self.items()}

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
        token = d['token']
        sort = KSort.from_dict(d['sort'])
        if sort == KSort('Bytes'):
            assert len(token) >= 3
            assert token[0:2] == 'b"'
            assert token[-1] == '"'
            token = 'b"' + dequote_str(token[2:-1]) + '"'
        if sort == KSort('String'):
            assert len(token) >= 2
            assert token[0] == '"'
            assert token[-1] == '"'
            token = '"' + dequote_str(token[1:-1]) + '"'
        return KToken(token=token, sort=sort)

    def to_dict(self) -> Dict[str, Any]:
        token = self.token
        if self.sort == KSort('Bytes'):
            assert len(token) >= 3
            assert token[0:2] == 'b"'
            assert token[-1] == '"'
            token = 'b"' + enquote_str(token[2:-1]) + '"'
        if self.sort == KSort('String'):
            assert len(token) >= 2
            assert token[0] == '"'
            assert token[-1] == '"'
            token = '"' + enquote_str(token[1:-1]) + '"'
        return {'node': 'KToken', 'token': token, 'sort': self.sort.to_dict()}

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
class KVariable(KInner):
    name: str
    sort: Optional[KSort]

    def __init__(self, name: str, *, sort: Optional[KSort] = None):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)

    @classmethod
    def from_dict(cls: Type['KVariable'], d: Dict[str, Any]) -> 'KVariable':
        cls._check_node(d)
        sort = None
        att = KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT
        for a in [
            KAtt.LOCATION,
            KAtt.SOURCE,
            'anonymous',
            'cellSort',
            'withConfig',
            'prettyPrintWithSortAnnotation',
            'fresh',
        ]:
            if a in att:
                _LOGGER.debug(f'Removing attribute from KVariable: {a}: {att[a]}, from KVariable {d}')
                att = att.remove([a])
        if KAtt.SORT in att:
            sort = KSort.from_dict(att[KAtt.SORT])
            if len(att) > 1:
                raise ValueError(f'Attributes other than {KAtt.SORT} attached to KVariable: {d}')
        elif len(att) > 0:
            raise ValueError(f'Attributes other than {KAtt.SORT} attached to KVariable: {d}')
        return KVariable(name=d['name'], sort=sort)

    def to_dict(self) -> Dict[str, Any]:
        _att = KAtt({})
        if self.sort is not None:
            _att = _att.update({KAtt.SORT: self.sort.to_dict()})
        return {'node': 'KVariable', 'name': self.name, 'att': _att.to_dict()}

    def let(self, *, name: Optional[str] = None, sort: Optional[KSort] = None) -> 'KVariable':
        name = name if name is not None else self.name
        sort = sort if sort is not None else self.sort
        return KVariable(name=name, sort=sort)

    def let_sort(self, sort: Optional[KSort]) -> 'KVariable':
        return KVariable(self.name, sort=sort)

    def map_inner(self: 'KVariable', f: Callable[[KInner], KInner]) -> 'KVariable':
        return self

    def match(self, term: KInner) -> Subst:
        return Subst({self.name: term})


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
                raise TypeError(f'KLabel() got an unexpected keyword argument: {bad_arg}')
            if args:
                raise TypeError('KLabel() got multiple values for argument: params')
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
                raise TypeError(f'KApply() got an unexpected keyword argument: {bad_arg}')
            if args:
                raise TypeError('KApply() got multiple values for argument: args')
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
                raise TypeError(f'KSequence() got an unexpected keyword argument: {bad_arg}')
            if args:
                raise TypeError('KSequence() got multiple values for argument: items')
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


# TODO make method of KInner
def bottom_up(f: Callable[[KInner], KInner], kinner: KInner) -> KInner:
    return f(kinner.map_inner(lambda _kinner: bottom_up(f, _kinner)))


# TODO make method of KInner
def top_down(f: Callable[[KInner], KInner], kinner: KInner) -> KInner:
    return f(kinner).map_inner(lambda _kinner: top_down(f, _kinner))


# TODO: make method of KInner
def var_occurrences(term: KInner) -> Dict[str, List[KVariable]]:
    _var_occurrences: Dict[str, List[KVariable]] = {}

    # TODO: should treat #Exists and #Forall specially.
    def _var_occurence(_term: KInner) -> None:
        if type(_term) is KVariable:
            if _term.name not in _var_occurrences:
                _var_occurrences[_term.name] = []
            _var_occurrences[_term.name].append(_term)

    collect(_var_occurence, term)
    return _var_occurrences


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
