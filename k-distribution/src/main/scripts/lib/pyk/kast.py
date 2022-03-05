import json
import sys
from abc import ABC, abstractmethod
from dataclasses import InitVar, dataclass
from enum import Enum
from itertools import chain
from typing import (
    Any,
    Callable,
    Dict,
    Final,
    FrozenSet,
    Iterable,
    Iterator,
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

from typing_extensions import TypeAlias

from .cli_utils import fatal, warning

T = TypeVar('T', bound='KAst')


class KAst(ABC):

    @classmethod
    @abstractmethod
    def from_dict(cls: Type[T], d: Dict[str, Any]) -> 'KAst':
        node = d['node']
        return globals()[node].from_dict(d)

    @abstractmethod
    def to_dict(self) -> Dict[str, Any]:
        ...

    @staticmethod
    def from_json(s: str) -> 'KAst':
        return KAst.from_dict(json.loads(s))

    @final
    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True)

    @classmethod
    def _check_node(cls: Type[T], d: Dict[str, Any], expected: Optional[str] = None) -> None:
        expected = expected if expected is not None else cls.__name__
        actual = d['node']
        if actual != expected:
            raise ValueError(f"Expected '{expected}' as 'node' value, found: '{actual}'")


@final
@dataclass(frozen=True)
class KAtt(KAst, Mapping[str, Any]):
    _atts: FrozenSet[Tuple[str, Any]]

    def __init__(self, atts: Mapping[str, Any] = {}):
        object.__setattr__(self, '_atts', frozenset(atts.items()))

    def __getitem__(self, key: str) -> Any:
        return self.atts[key]

    def __iter__(self) -> Iterator[str]:
        return (k for k, _ in self._atts)

    def __len__(self) -> int:
        return len(self._atts)

    @property
    def atts(self) -> Dict[str, Any]:
        return dict(self._atts)

    @staticmethod
    def of(**atts: Any) -> 'KAtt':
        return KAtt(atts=atts)

    @classmethod
    def from_dict(cls: Type['KAtt'], d: Dict[str, Any]) -> 'KAtt':
        cls._check_node(d)
        return KAtt(atts=d['att'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KAtt', 'att': self.atts}

    def let(self, *, atts: Optional[Mapping[str, Any]] = None) -> 'KAtt':
        atts = atts if atts is not None else self.atts
        return KAtt(atts=atts)

    def update(self, atts: Mapping[str, Any]) -> 'KAtt':
        return self.let(atts={k: v for k, v in {**self.atts, **atts}.items() if v is not None})


EMPTY_ATT: Final = KAtt()


W = TypeVar('W', bound='WithKAtt')
KI = TypeVar('KI', bound='KInner')


class WithKAtt(KAst, ABC):
    att: KAtt

    @abstractmethod
    def let_att(self: W, att: KAtt) -> W:
        ...

    def map_att(self: W, f: Callable[[KAtt], KAtt]) -> W:
        if self.att is None:
            return self
        return self.let_att(att=f(self.att))

    def update_atts(self: W, atts: Mapping[str, Any]) -> W:
        if self.att is None:
            return self.let_att(att=KAtt.of(**atts))
        return self.let_att(att=self.att.update(atts))


class KInner(KAst, ABC):
    _INNER_NODES: Final = {'KVariable', 'KSort', 'KToken', 'KApply', 'KAs', 'KRewrite', 'KSequence'}

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


K: TypeAlias = KInner


@final
@dataclass(frozen=True)
class KVariable(KInner):
    name: str

    def __init__(self, name: str):
        object.__setattr__(self, 'name', name)

    @classmethod
    def from_dict(cls: Type['KVariable'], d: Dict[str, Any]) -> 'KVariable':
        cls._check_node(d)
        return KVariable(name=d['name'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KVariable', 'name': self.name, 'originalName': self.name}

    def let(self, *, name: Optional[str] = None) -> 'KVariable':
        name = name if name is not None else self.name
        return KVariable(name=name)

    def map_inner(self: 'KVariable', f: Callable[[KInner], KInner]) -> 'KVariable':
        return self


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
        return {'node': 'KSort', 'name': self.name, 'originalName': self.name}

    def let(self, *, name: Optional[str] = None) -> 'KSort':
        name = name if name is not None else self.name
        return KSort(name=name)

    def map_inner(self: 'KSort', f: Callable[[KInner], KInner]) -> 'KSort':
        return self


BOOL = KSort('Bool')
INT = KSort('Int')
STRING = KSort('String')


@final
@dataclass(frozen=True)
class KToken(KInner):
    token: str
    sort: str

    def __init__(self, token: str, sort: str):
        object.__setattr__(self, 'token', token)
        object.__setattr__(self, 'sort', sort)

    @classmethod
    def from_dict(cls: Type['KToken'], d: Dict[str, Any]) -> 'KToken':
        cls._check_node(d)
        return KToken(token=d['token'], sort=d['sort'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KToken', 'token': self.token, 'sort': self.sort}

    def let(self, *, token: Optional[str] = None, sort: Optional[str] = None) -> 'KToken':
        token = token if token is not None else self.token
        sort = sort if sort is not None else self.sort
        return KToken(token=token, sort=sort)

    def map_inner(self: 'KToken', f: Callable[[KInner], KInner]) -> 'KToken':
        return self


TRUE = KToken('true', 'Bool')
FALSE = KToken('false', 'Bool')


@final
@dataclass(frozen=True)
class KApply(KInner):
    label: str
    args: Tuple[KInner, ...]

    def __init__(self, label: str, args: Iterable[KInner] = ()):
        object.__setattr__(self, 'label', label)
        object.__setattr__(self, 'args', tuple(args))

    def __iter__(self) -> Iterator[Union[str, KInner]]:
        return chain([self.label], self.args)

    @property
    def arity(self) -> int:
        return len(self.args)

    @property
    def is_cell(self) -> bool:
        return len(self.label) > 1 and self.label[0] == '<' and self.label[-1] == '>'

    @staticmethod
    def of(label: str, *args: KInner) -> 'KApply':
        return KApply(label=label, args=args)

    @classmethod
    def from_dict(cls: Type['KApply'], d: Dict[str, Any]) -> 'KApply':
        cls._check_node(d)
        return KApply(label=d['label'], args=(KInner.from_dict(arg) for arg in d['args']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KApply', 'label': self.label, 'args': [arg.to_dict() for arg in self.args], 'arity': self.arity, 'variable': False}

    def let(self, *, label: Optional[str] = None, args: Optional[Iterable[KInner]] = None) -> 'KApply':
        label = label if label is not None else self.label
        args = args if args is not None else self.args
        return KApply(label=label, args=args)

    def map_inner(self: 'KApply', f: Callable[[KInner], KInner]) -> 'KApply':
        return self.let(args=(f(arg) for arg in self.args))


TOP: Final = KApply('#Top')
BOTTOM: Final = KApply('#Bottom')


@final
@dataclass(frozen=True)
class KAs(KInner, WithKAtt):
    pattern: KInner
    alias: KInner
    att: KAtt

    def __init__(self, pattern: KInner, alias: KInner, att=EMPTY_ATT):
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'alias', alias)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KAs'], d: Dict[str, Any]) -> 'KAs':
        cls._check_node(d)
        return KAs(pattern=KInner.from_dict(d['pattern']), alias=KInner.from_dict(d['alias']), att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT)

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KAs', 'pattern': self.pattern.to_dict(), 'alias': self.alias.to_dict(), 'att': self.att.to_dict()}

    def let(self, *, pattern: Optional[KInner] = None, alias: Optional[KInner] = None, att: Optional[KAtt] = None) -> 'KAs':
        pattern = pattern if pattern is not None else self.pattern
        alias = alias if alias is not None else self.alias
        att = att if att is not None else self.att
        return KAs(pattern=pattern, alias=alias, att=att)

    def let_att(self, att: KAtt) -> 'KAs':
        return self.let(att=att)

    def map_inner(self: 'KAs', f: Callable[[KInner], KInner]) -> 'KAs':
        return self.let(pattern=f(self.pattern), alias=f(self.alias))


@final
@dataclass(frozen=True)
class KRewrite(KInner):
    lhs: KInner
    rhs: KInner

    def __init__(self, lhs: KInner, rhs: KInner):
        object.__setattr__(self, 'lhs', lhs)
        object.__setattr__(self, 'rhs', rhs)

    def __iter__(self) -> Iterator[KInner]:
        return iter([self.lhs, self.rhs])

    @classmethod
    def from_dict(cls: Type['KRewrite'], d: Dict[str, Any]) -> 'KRewrite':
        cls._check_node(d)
        return KRewrite(lhs=KInner.from_dict(d['lhs']), rhs=KInner.from_dict(d['rhs']))

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KRewrite', 'lhs': self.lhs.to_dict(), 'rhs': self.rhs.to_dict()}

    def let(self, *, lhs: Optional[KInner] = None, rhs: Optional[KInner] = None) -> 'KRewrite':
        lhs = lhs if lhs is not None else self.lhs
        rhs = rhs if rhs is not None else self.rhs
        return KRewrite(lhs=lhs, rhs=rhs)

    def map_inner(self: 'KRewrite', f: Callable[[KInner], KInner]) -> 'KRewrite':
        return self.let(lhs=f(self.lhs), rhs=f(self.rhs))


@final
@dataclass(frozen=True)
class KSequence(KInner, Sequence[KInner]):
    items: Tuple[KInner, ...]

    def __init__(self, items: Iterable[KInner] = ()):
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

    @staticmethod
    def of(*items: KInner) -> 'KSequence':
        return KSequence(items=items)

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


class KOuter(KAst, ABC):
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


class KProductionItem(KOuter, ABC):
    _PRODUCTION_ITEM_NODES: Final = {'KTerminal', 'KRegexTerminal', 'KNonTerminal'}

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KProductionItem'], d: Dict[str, Any]) -> 'KProductionItem':
        node = d['node']
        if node in KProductionItem._PRODUCTION_ITEM_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f"Expected KProductionItem label as 'node' value, found: '{node}'")


class KSentence(KOuter, WithKAtt, ABC):
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

    def __init__(self, regex: str, precede_regex: str = '', follow_regex: str = ''):
        object.__setattr__(self, 'regex', regex)
        object.__setattr__(self, 'precede_regex', precede_regex)
        object.__setattr__(self, 'follow_regex', follow_regex)

    @classmethod
    def from_dict(cls: Type['KRegexTerminal'], d: Dict[str, Any]) -> 'KRegexTerminal':
        cls._check_node(d)
        return KRegexTerminal(
            regex=d['regex'],
            precede_regex=d.get('precede_regex', ''),
            follow_regex=d.get('follow_regex', ''),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KRegexTerminal', 'regex': self.regex, 'precedeRegex': self.precede_regex or None, 'follow_regex': self.follow_regex or None}

    # TODO consider nullable fields and make sure their value can be erased
    def let(self, *, regex: Optional[str] = None, precede_regex: Optional[str] = None, follow_regex: Optional[str] = None) -> 'KRegexTerminal':
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
    sort: KSort
    items: Tuple[KProductionItem, ...]
    klabel: str
    att: KAtt

    def __init__(self, sort: KSort, items: Iterable[KProductionItem] = (), klabel='', att=EMPTY_ATT):
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'items', tuple(items))
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
            klabel=d.get('klabel', ''),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            'node': 'KProduction',
            'sort': self.sort.to_dict(),
            'productionItems': [item.to_dict() for item in self.items],
            'klabel': self.klabel or None,
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        sort: Optional[KSort] = None,
        items: Optional[Iterable[KProductionItem]] = None,
        klabel: Optional[str] = None,
        att: Optional[KAtt] = None,
    ) -> 'KProduction':
        sort = sort or self.sort
        items = items if items is not None else self.items
        klabel = klabel if klabel is not None else self.klabel
        att = att if att is not None else self.att
        return KProduction(sort=sort, items=items, klabel=klabel, att=att)

    def let_att(self, att: KAtt) -> 'KProduction':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSyntaxSort(KSentence):
    sort: KSort
    att: KAtt

    def __init__(self, sort: KSort, att=EMPTY_ATT):
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: Type['KSyntaxSort'], d: Dict[str, Any]) -> 'KSyntaxSort':
        cls._check_node(d)
        return KSyntaxSort(sort=KSort.from_dict(d['sort']), att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT)

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KSyntaxSort', 'sort': self.sort.to_dict(), 'att': self.att.to_dict()}

    def let(self, *, sort: Optional[KSort] = None, att: Optional[KAtt] = None) -> 'KSyntaxSort':
        sort = sort or self.sort
        att = att if att is not None else self.att
        return KSyntaxSort(sort=sort, att=att)

    def let_att(self, att: KAtt) -> 'KSyntaxSort':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSortSynonym(KSentence):
    new_sort: KSort
    old_sort: KSort
    att: KAtt

    def __init__(self, new_sort: KSort, old_sort: KSort, att=EMPTY_ATT):
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

    def let(self, *, old_sort: Optional[KSort] = None, new_sort: Optional[KSort] = None, att: Optional[KAtt] = None) -> 'KSortSynonym':
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

    def __init__(self, name: str, regex: str, att=EMPTY_ATT):
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

    def let(self, *, name: Optional[str] = None, regex: Optional[str] = None, att: Optional[KAtt] = None) -> 'KSyntaxLexical':
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

    def __init__(self, assoc: KAssoc, tags: Iterable[str] = frozenset(), att=EMPTY_ATT):
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
        return {'node': 'KSyntaxAssociativity', 'assoc': self.assoc.value, 'tags': list(self.tags), 'att': self.att.to_dict()}

    def let(self, *, assoc: Optional[KAssoc] = None, tags: Optional[Iterable[str]] = None, att: Optional[KAtt] = None) -> 'KSyntaxAssociativity':
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

    def __init__(self, priorities: Iterable[Iterable[str]] = (), att=EMPTY_ATT):
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
        return {'node': 'KSyntaxPriority', 'priorities': [list(group) for group in self.priorities], 'att': self.att.to_dict()}

    def let(self, *, priorities: Optional[Iterable[Iterable[str]]] = None, att: Optional[KAtt] = None) -> 'KSyntaxPriority':
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

    def __init__(self, sentence_type: str, content: str, att=EMPTY_ATT):
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

    def let(self, *, sentence_type: Optional[str] = None, content: Optional[str] = None, att: Optional[KAtt] = None) -> 'KBubble':
        sentence_type = sentence_type if sentence_type is not None else self.sentence_type
        content = content if content is not None else self.content
        att = att if att is not None else self.att
        return KBubble(sentence_type=sentence_type, content=content, att=att)

    def let_att(self, att: KAtt) -> 'KBubble':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KRule(KSentence):
    body: KInner
    requires: KInner
    ensures: KInner
    att: KAtt

    def __init__(self, body: KInner, requires: KInner = TRUE, ensures: KInner = TRUE, att=EMPTY_ATT):
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

    def let(self, *, body: Optional[KInner] = None, requires: Optional[KInner] = None, ensures: Optional[KInner] = None, att: Optional[KAtt] = None) -> 'KRule':
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        ensures = ensures if ensures is not None else self.ensures
        att = att if att is not None else self.att
        return KRule(body=body, requires=requires, ensures=ensures, att=att)

    def let_att(self, att: KAtt) -> 'KRule':
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KClaim(KSentence):
    body: KInner
    requires: KInner
    ensures: KInner
    att: KAtt

    def __init__(self, body: KInner, requires: KInner = TRUE, ensures: KInner = TRUE, att=EMPTY_ATT):
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

    def let(self, *, body: Optional[KInner] = None, requires: Optional[KInner] = None, ensures: Optional[KInner] = None, att: Optional[KAtt] = None) -> 'KClaim':
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

    def __init__(self, body: KInner, requires: KInner = TRUE, att=EMPTY_ATT):
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

    def let(self, *, body: Optional[KInner] = None, requires: Optional[KInner] = None, att: Optional[KAtt] = None) -> 'KContext':
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

    def __init__(self, name: str, public: bool):
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

    def __init__(self, name: str, sentences: Iterable[KSentence] = (), imports: Iterable[KImport] = (), att=EMPTY_ATT):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'imports', tuple(imports))
        object.__setattr__(self, 'att', att)

    def __iter__(self) -> Iterator[KSentence]:
        return iter(self.sentences)

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

    def __init__(self, main_module_name: str, modules: Iterable[KFlatModule], requires: Iterable[KRequire] = (), att=EMPTY_ATT):
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


def flattenLabel(label, kast):
    """Given a cons list, return a flat Python list of the elements.

    -   Input: Cons operation to flatten.
    -   Output: Items of cons list.
    """
    if type(kast) is KApply and kast.label == label:
        items = [flattenLabel(label, arg) for arg in kast.args]
        return [c for cs in items for c in cs]
    return [kast]


klabelCells = '#KCells'
klabelEmptyK = '#EmptyK'
ktokenDots = KToken('...', 'K')


def paren(printer):
    return (lambda *args: '( ' + printer(*args) + ' )')


def binOpStr(symbol):
    return (lambda a1, a2: a1 + ' ' + symbol + ' ' + a2)


def appliedLabelStr(symbol):
    return (lambda *args: symbol + ' ( ' + ' , '.join(args) + ' )')


def constLabel(symbol):
    return (lambda: symbol)


def assocWithUnit(assocJoin, unit):
    def _assocWithUnit(*args):
        newArgs = [arg for arg in args if arg != unit]
        return assocJoin.join(newArgs)
    return _assocWithUnit


def underbarUnparsing(symbol):
    splitSymbol = symbol.split('_')

    def _underbarUnparsing(*args):
        result = []
        i = 0
        for symb in splitSymbol:
            if symb != '':
                result.append(symb)
            if i < len(args):
                result.append(args[i])
                i += 1
        return ' '.join(result)

    return _underbarUnparsing


def indent(input, size=2):
    return '\n'.join([(' ' * size) + line for line in input.split('\n')])


def newLines(input):
    return '\n'.join(input)


def buildSymbolTable(definition, opinionated=False):
    """Build the unparsing symbol table given a JSON encoded definition.

    -   Input: JSON encoded K definition.
    -   Return: Python dictionary mapping klabels to automatically generated unparsers.
    """
    if type(definition) is not KDefinition:
        fatal('Must supply a KDefinition!')

    def _unparserFromProductionItems(prodItems):
        unparseString = ''
        for prodItem in prodItems:
            if type(prodItem) is KTerminal:
                unparseString += prodItem.value
            elif type(prodItem) is KNonTerminal:
                unparseString += '_'
        return underbarUnparsing(unparseString)

    symbolTable = {}
    for module in definition.modules:
        for sentence in module.sentences:
            if type(sentence) is KProduction and sentence.klabel:
                label = sentence.klabel
                if 'symbol' in sentence.att and 'klabel' in sentence.att:
                    label = sentence.att['klabel']
                unparser = _unparserFromProductionItems(sentence.items)
                symbolTable[label] = unparser

    if opinionated:
        symbolTable['#And'] = lambda c1, c2: c1 + '\n#And ' + c2
        symbolTable['#Or'] = lambda c1, c2: c1 + '\n#Or\n' + indent(c2, size=4)

    return symbolTable


def readKastTerm(termPath):
    with open(termPath, 'r') as termFile:
        return KAst.from_dict(json.loads(termFile.read())['term'])


def prettyPrintKastBool(kast, symbolTable, debug=False):
    """Print out KAST requires/ensures clause.

    -   Input: KAST Bool for requires/ensures clause.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if type(kast) is KApply and kast.label in ['_andBool_', '_orBool_']:
        clauses = [prettyPrintKastBool(c, symbolTable, debug=debug) for c in flattenLabel(kast.label, kast)]
        head = kast.label.replace('_', ' ')
        if head == ' orBool ':
            head = '  orBool '
        separator = ' ' * (len(head) - 7)
        spacer = ' ' * len(head)

        def joinSep(s):
            return ('\n' + separator).join(s.split('\n'))

        clauses = ['( ' + joinSep(clauses[0])] + [head + '( ' + joinSep(c) for c in clauses[1:]] + [spacer + (')' * len(clauses))]
        return '\n'.join(clauses)
    else:
        return prettyPrintKast(kast, symbolTable, debug=debug)


def prettyPrintKast(kast, symbolTable, debug=False):
    """Print out KAST terms/outer syntax.

    -   Input: KAST term.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if kast is None or kast == {}:
        return ""
    if type(kast) is KVariable:
        return kast.name
    if type(kast) is KSort:
        return kast.name
    if type(kast) is KToken:
        return kast.token
    if type(kast) is KApply:
        label = kast.label
        args = kast.args
        unparsedArgs = [prettyPrintKast(arg, symbolTable, debug=debug) for arg in args]
        if kast.is_cell:
            cellContents = '\n'.join(unparsedArgs).rstrip()
            cellStr = label + '\n' + indent(cellContents) + '\n</' + label[1:]
            return cellStr.rstrip()
        unparser = appliedLabelStr(label) if label not in symbolTable else symbolTable[label]
        return unparser(*unparsedArgs)
    if type(kast) is KAs:
        patternStr = prettyPrintKast(kast.pattern, symbolTable, debug=debug)
        aliasStr = prettyPrintKast(kast.alias, symbolTable, debug=debug)
        return patternStr + ' #as ' + aliasStr
    if type(kast) is KRewrite:
        lhsStr = prettyPrintKast(kast.lhs, symbolTable, debug=debug)
        rhsStr = prettyPrintKast(kast.rhs, symbolTable, debug=debug)
        return '( ' + lhsStr + ' => ' + rhsStr + ' )'
    if type(kast) is KSequence:
        if kast.arity == 0:
            return prettyPrintKast(KApply(klabelEmptyK), symbolTable, debug=debug)
        if kast.arity == 1:
            return prettyPrintKast(kast.items[0], symbolTable, debug=debug)
        unparsedKSequence = '\n~> '.join([prettyPrintKast(item, symbolTable, debug=debug) for item in kast.items[0:-1]])
        if kast.items[-1] == ktokenDots:
            unparsedKSequence = unparsedKSequence + '\n' + prettyPrintKast(ktokenDots, symbolTable, debug=debug)
        else:
            unparsedKSequence = unparsedKSequence + '\n~> ' + prettyPrintKast(kast.items[-1], symbolTable, debug=debug)
        return unparsedKSequence
    if type(kast) is KTerminal:
        return '"' + kast.value + '"'
    if type(kast) is KRegexTerminal:
        return 'r"' + kast.regex + '"'
    if type(kast) is KNonTerminal:
        return prettyPrintKast(kast.sort, symbolTable, debug=debug)
    if type(kast) is KProduction:
        if 'klabel' not in kast.att and kast.klabel:
            kast = kast.update_atts({'klabel': kast.klabel})
        sortStr = prettyPrintKast(kast.sort, symbolTable, debug=debug)
        productionStr = ' '.join([prettyPrintKast(pi, symbolTable, debug=debug) for pi in kast.items])
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        return 'syntax ' + sortStr + ' ::= ' + productionStr + ' ' + attStr
    if type(kast) is KSyntaxSort:
        sortStr = prettyPrintKast(kast.sort, symbolTable, debug=debug)
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        return 'syntax ' + sortStr + ' ' + attStr
    if type(kast) is KSortSynonym:
        newSortStr = prettyPrintKast(kast.new_sort, symbolTable, debug=debug)
        oldSortStr = prettyPrintKast(kast.old_sort, symbolTable, debug=debug)
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        return 'syntax ' + newSortStr + ' = ' + oldSortStr + ' ' + attStr
    if type(kast) is KSyntaxLexical:
        nameStr = kast.name
        regexStr = kast.regex
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        # todo: proper escaping
        return 'syntax lexical ' + nameStr + ' = r"' + regexStr + '" ' + attStr
    if type(kast) is KSyntaxAssociativity:
        assocStr = kast.assoc.value
        tagsStr = ' '.join(kast.tags)
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        return 'syntax associativity ' + assocStr + ' ' + tagsStr + ' ' + attStr
    if type(kast) is KSyntaxPriority:
        prioritiesStr = ' > '.join([' '.join(group) for group in kast.priorities])
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        return 'syntax priority ' + prioritiesStr + ' ' + attStr
    if type(kast) is KBubble:
        body = '// KBubble(' + kast.sentence_type + ', ' + kast.contents + ')'
        attStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        return body + ' ' + attStr
    if type(kast) is KRule or type(kast) is KClaim:
        body = '\n     '.join(prettyPrintKast(kast.body, symbolTable, debug=debug).split('\n'))
        ruleStr = 'rule ' if type(kast) is KRule else 'claim '
        if 'label' in kast.att:
            ruleStr = ruleStr + '[' + kast.att['label'] + ']:'
        ruleStr = ruleStr + ' ' + body
        attsStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        if kast.requires != TRUE:
            requiresStr = 'requires ' + '\n  '.join(prettyPrintKastBool(kast.requires, symbolTable, debug=debug).split('\n'))
            ruleStr = ruleStr + '\n  ' + requiresStr
        if kast.ensures != TRUE:
            ensuresStr = 'ensures ' + '\n  '.join(prettyPrintKastBool(kast.ensures, symbolTable, debug=debug).split('\n'))
            ruleStr = ruleStr + '\n   ' + ensuresStr
        return ruleStr + '\n  ' + attsStr
    if type(kast) is KContext:
        body = indent(prettyPrintKast(kast.body, symbolTable, debug=debug))
        contextStr = 'context alias ' + body
        requiresStr = ''
        attsStr = prettyPrintKast(kast.att, symbolTable, debug=debug)
        if kast.requires != TRUE:
            requiresStr = prettyPrintKast(kast.requires, symbolTable, debug=debug)
            requiresStr = 'requires ' + indent(requiresStr)
        return contextStr + '\n  ' + requiresStr + '\n  ' + attsStr
    if type(kast) is KAtt:
        if not kast.atts:
            return ''
        attStrs = [k + '(' + v + ')' for k, v in kast.atts.items()]
        return '[' + ', '.join(attStrs) + ']'
    if type(kast) is KImport:
        return ' '.join(['imports', ('public' if kast.public else 'private'), kast.name])
    if type(kast) is KFlatModule:
        name = kast.name
        imports = '\n'.join([prettyPrintKast(kimport, symbolTable, debug=debug) for kimport in kast.imports])
        sentences = '\n\n'.join([prettyPrintKast(sentence, symbolTable, debug=debug) for sentence in kast.sentences])
        contents = imports + '\n\n' + sentences
        return 'module ' + name + '\n    ' + '\n    '.join(contents.split('\n')) + '\n\nendmodule'
    if type(kast) is KRequire:
        return 'requires "' + kast.require + '"'
    if type(kast) is KDefinition:
        requires = '\n'.join([prettyPrintKast(require, symbolTable, debug=debug) for require in kast.requires])
        modules = '\n\n'.join([prettyPrintKast(module, symbolTable, debug=debug) for module in kast.modules])
        return requires + '\n\n' + modules

    print()
    warning('Error unparsing kast!')
    print(kast)
    fatal('Error unparsing!')
