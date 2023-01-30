import json
import logging
from abc import abstractmethod
from dataclasses import InitVar, dataclass
from enum import Enum
from functools import cached_property
from os import PathLike
from typing import (
    Any,
    Dict,
    Final,
    FrozenSet,
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

from ..prelude.kbool import TRUE
from ..utils import filter_none, single, unique
from .inner import (
    KApply,
    KInner,
    KLabel,
    KRewrite,
    KSequence,
    KSort,
    KToken,
    KVariable,
    Subst,
    bottom_up,
    collect,
    top_down,
    var_occurrences,
)
from .kast import EMPTY_ATT, KAst, KAtt, WithKAtt

RL = TypeVar('RL', bound='KRuleLike')

_LOGGER: Final = logging.getLogger(__name__)


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
    def from_dict(cls: Type['KOuter'], d: Mapping[str, Any]) -> 'KOuter':
        node = d['node']
        if node in KOuter._OUTER_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected "node" value in: {KOuter._OUTER_NODES}, got: {node}')


class KProductionItem(KOuter):
    _PRODUCTION_ITEM_NODES: Final = {'KTerminal', 'KRegexTerminal', 'KNonTerminal'}

    @classmethod
    @abstractmethod
    def from_dict(cls: Type['KProductionItem'], d: Mapping[str, Any]) -> 'KProductionItem':
        node = d['node']
        if node in KProductionItem._PRODUCTION_ITEM_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected "node" value in: {KProductionItem._PRODUCTION_ITEM_NODES}, got: {node}')


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
    def from_dict(cls: Type['KSentence'], d: Mapping[str, Any]) -> 'KSentence':
        node = d['node']
        if node in KSentence._SENTENCE_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected "node" value in: {KSentence._SENTENCE_NODES}, got: {node}')

    @property
    def label(self) -> str:
        if 'label' in self.att:
            return self.att['label']
        elif 'UNIQUE_ID' in self.att:
            return self.att['UNIQUE_ID']
        else:
            _LOGGER.warning(f'Found a sentence without label or UNIQUE_ID: {self}')
            if KAtt.SOURCE in self.att and KAtt.LOCATION in self.att:
                return f'{self.att[KAtt.SOURCE]}:{self.att[KAtt.LOCATION]}'
            else:
                raise ValueError(f'Found sentence without label, UNIQUE_ID, or SOURCE:LOCATION: {self}')


@final
@dataclass(frozen=True)
class KTerminal(KProductionItem):
    value: str

    def __init__(self, value: str):
        object.__setattr__(self, 'value', value)

    @classmethod
    def from_dict(cls: Type['KTerminal'], d: Mapping[str, Any]) -> 'KTerminal':
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
    def from_dict(cls: Type['KRegexTerminal'], d: Mapping[str, Any]) -> 'KRegexTerminal':
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
    def from_dict(cls: Type['KNonTerminal'], d: Mapping[str, Any]) -> 'KNonTerminal':
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

    @property
    def argument_sorts(self) -> List[KSort]:
        return [knt.sort for knt in self.items if type(knt) is KNonTerminal]

    @classmethod
    def from_dict(cls: Type['KProduction'], d: Mapping[str, Any]) -> 'KProduction':
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
    def from_dict(cls: Type['KSyntaxSort'], d: Mapping[str, Any]) -> 'KSyntaxSort':
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
    def from_dict(cls: Type['KSortSynonym'], d: Mapping[str, Any]) -> 'KSortSynonym':
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
    def from_dict(cls: Type['KSyntaxLexical'], d: Mapping[str, Any]) -> 'KSyntaxLexical':
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
    def from_dict(cls: Type['KSyntaxAssociativity'], d: Mapping[str, Any]) -> 'KSyntaxAssociativity':
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
    def from_dict(cls: Type['KSyntaxPriority'], d: Mapping[str, Any]) -> 'KSyntaxPriority':
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
    def from_dict(cls: Type['KBubble'], d: Mapping[str, Any]) -> 'KBubble':
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
    def from_dict(cls: Type['KRuleLike'], d: Mapping[str, Any]) -> 'KRuleLike':
        node = d['node']
        if node in KRuleLike._RULE_LIKE_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected "node" value in: {KRuleLike._RULE_LIKE_NODES}, got: {node}')

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
    def from_dict(cls: Type['KRule'], d: Mapping[str, Any]) -> 'KRule':
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
    def from_dict(cls: Type['KClaim'], d: Mapping[str, Any]) -> 'KClaim':
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
    def from_dict(cls: Type['KContext'], d: Mapping[str, Any]) -> 'KContext':
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
    def from_dict(cls: Type['KImport'], d: Mapping[str, Any]) -> 'KImport':
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
class KFlatModule(KOuter, WithKAtt, Iterable[KSentence]):
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

    @cached_property
    def productions(self) -> Tuple[KProduction, ...]:
        return tuple(sentence for sentence in self if type(sentence) is KProduction)

    @cached_property
    def syntax_productions(self) -> Tuple[KProduction, ...]:
        return tuple(prod for prod in self.productions if prod.klabel)

    @cached_property
    def functions(self) -> Tuple[KProduction, ...]:
        return tuple(prod for prod in self.syntax_productions if self._is_function(prod))

    @cached_property
    def constructors(self) -> Tuple[KProduction, ...]:
        return tuple(prod for prod in self.syntax_productions if not self._is_function(prod))

    @staticmethod
    def _is_function(prod: KProduction) -> bool:
        def is_not_actually_function(label: str) -> bool:
            is_cell_map_constructor = label.endswith('CellMapItem') or label.endswith('CellMap_')
            is_builtin_data_constructor = label in {'_Set_', '_List_', '_Map_', 'SetItem', 'ListItem', '_|->_'}
            return is_cell_map_constructor or is_builtin_data_constructor

        return ('function' in prod.att.atts or 'functional' in prod.att.atts) and not (
            prod.klabel and is_not_actually_function(prod.klabel.name)
        )

    @cached_property
    def rules(self) -> Tuple[KRule, ...]:
        return tuple(sentence for sentence in self if type(sentence) is KRule)

    @cached_property
    def claims(self) -> Tuple[KClaim, ...]:
        return tuple(sentence for sentence in self if type(sentence) is KClaim)

    @classmethod
    def from_dict(cls: Type['KFlatModule'], d: Mapping[str, Any]) -> 'KFlatModule':
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
        object.__setattr__(self, 'modules', tuple(modules))

    @classmethod
    def from_dict(cls: Type['KFlatModuleList'], d: Mapping[str, Any]) -> 'KFlatModuleList':
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
    def from_dict(cls: Type['KRequire'], d: Mapping[str, Any]) -> 'KRequire':
        cls._check_node(d)
        return KRequire(require=d['require'])

    def to_dict(self) -> Dict[str, Any]:
        return {'node': 'KRequire', 'require': self.require}

    def let(self, *, require: Optional[str] = None) -> 'KRequire':
        require = require if require is not None else self.require
        return KRequire(require=require)


@final
@dataclass(frozen=True)
class KDefinition(KOuter, WithKAtt, Iterable[KFlatModule]):
    main_module_name: str
    modules: Tuple[KFlatModule, ...]
    requires: Tuple[KRequire, ...]
    att: KAtt

    main_module: InitVar[KFlatModule]

    _production_for_klabel: Dict[KLabel, KProduction]
    _subsorts: Dict[KSort, List[KSort]]
    _init_config: Dict[KSort, KInner]
    _empty_config: Dict[KSort, KInner]

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
            raise ValueError(f'Module not found: {main_module_name}')
        if len(main_modules) > 1:
            raise ValueError(f'Module is not unique: {main_module_name}')

        main_module = main_modules[0]

        object.__setattr__(self, 'main_module_name', main_module_name)
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'requires', tuple(requires))
        object.__setattr__(self, 'att', att)
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, '_production_for_klabel', {})
        object.__setattr__(self, '_subsorts', {})
        object.__setattr__(self, '_init_config', {})
        object.__setattr__(self, '_empty_config', {})

    def __iter__(self) -> Iterator[KFlatModule]:
        return iter(self.modules)

    @classmethod
    def from_dict(cls: Type['KDefinition'], d: Mapping[str, Any]) -> 'KDefinition':
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

    @cached_property
    def module_names(self) -> Tuple[str, ...]:
        return tuple(module.name for module in self)

    @cached_property
    def productions(self) -> Tuple[KProduction, ...]:
        return tuple(prod for module in self for prod in module.productions)

    @cached_property
    def syntax_productions(self) -> Tuple[KProduction, ...]:
        return tuple(prod for module in self for prod in module.syntax_productions)

    @cached_property
    def functions(self) -> Tuple[KProduction, ...]:
        return tuple(func for module in self for func in module.functions)

    @cached_property
    def constructors(self) -> Tuple[KProduction, ...]:
        return tuple(ctor for module in self for ctor in module.constructors)

    @cached_property
    def rules(self) -> Tuple[KRule, ...]:
        return tuple(rule for module in self for rule in module.rules)

    @cached_property
    def alias_rules(self) -> Tuple[KRule, ...]:
        return tuple(rule for rule in self.rules if 'alias' in rule.att)

    @cached_property
    def macro_rules(self) -> Tuple[KRule, ...]:
        return tuple(rule for rule in self.rules if 'macro' in rule.att) + self.alias_rules

    @cached_property
    def semantic_rules(self) -> Tuple[KRule, ...]:
        def is_semantic(rule: KRule) -> bool:
            return (type(rule.body) is KApply and rule.body.label.name == '<generatedTop>') or (
                type(rule.body) is KRewrite
                and type(rule.body.lhs) is KApply
                and rule.body.lhs.label.name == '<generatedTop>'
            )

        return tuple(rule for rule in self.rules if is_semantic(rule))

    def production_for_klabel(self, klabel: KLabel) -> KProduction:
        if klabel not in self._production_for_klabel:
            prods = [prod for prod in self.productions if prod.klabel and prod.klabel.name == klabel.name]
            _prods = [prod for prod in prods if 'unparseAvoid' not in prod.att]
            if len(_prods) < len(prods):
                prods = _prods
                _LOGGER.warning(
                    f'Discarding {len(prods) - len(_prods)} productions with `unparseAvoid` attribute for label: {klabel}'
                )
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

    def module(self, name: str) -> KFlatModule:
        return single(module for module in self if module.name == name)

    def return_sort(self, label: KLabel) -> KSort:
        return self.production_for_klabel(label).sort

    def argument_sorts(self, label: KLabel) -> List[KSort]:
        return self.production_for_klabel(label).argument_sorts

    def subsorts(self, sort: KSort) -> List[KSort]:
        if sort not in self._subsorts:
            self._subsorts[sort] = self._compute_subsorts(sort)
        return self._subsorts[sort]

    def _compute_subsorts(self, sort: KSort) -> List[KSort]:
        _subsorts = []
        for prod in self.productions:
            if prod.sort == sort and len(prod.items) == 1 and type(prod.items[0]) is KNonTerminal:
                _subsort = prod.items[0].sort
                _subsorts.extend([_subsort] + self.subsorts(prod.items[0].sort))
        return list(set(_subsorts))

    def sort_vars_subst(self, kast: KInner) -> Subst:
        _var_sort_occurrences = var_occurrences(kast)
        subst = {}

        def _sort_contexts(_kast: KInner) -> None:
            if type(_kast) is KApply:
                prod = self.production_for_klabel(_kast.label)
                if len(prod.params) == 0:
                    for t, a in zip(prod.argument_sorts, _kast.args):
                        if type(a) is KVariable:
                            _var_sort_occurrences[a.name].append(a.let_sort(t))
            if type(_kast) is KSequence and _kast.arity > 0:
                for a in _kast.items[0:-1]:
                    if type(a) is KVariable:
                        _var_sort_occurrences[a.name].append(a.let_sort(KSort('KItem')))
                last_a = _kast.items[-1]
                if type(last_a) is KVariable:
                    _var_sort_occurrences[last_a.name].append(last_a.let_sort(KSort('K')))

        collect(_sort_contexts, kast)

        for vname, _voccurrences in _var_sort_occurrences.items():
            voccurrences = list(unique(_voccurrences))
            if len(voccurrences) > 0:
                vsort = voccurrences[0].sort
                if len(voccurrences) > 1:
                    for v in voccurrences[1:]:
                        if vsort is None and v.sort is not None:
                            vsort = v.sort
                        elif vsort is not None and v.sort is not None:
                            if vsort != v.sort:
                                if v.sort in self.subsorts(vsort):
                                    vsort = v.sort
                                elif vsort not in self.subsorts(v.sort):
                                    raise ValueError(
                                        f'Could not find common subsort among variable occurrences: {voccurrences}'
                                    )
                subst[vname] = KVariable(vname, sort=vsort)

        return Subst(subst)

    def sort_vars(self, kast: KInner) -> KInner:
        subst = self.sort_vars_subst(kast)
        return subst(kast)

    def empty_config(self, sort: KSort) -> KInner:
        if sort not in self._empty_config:
            self._empty_config[sort] = self._compute_empty_config(sort)
        return self._empty_config[sort]

    def _compute_empty_config(self, sort: KSort) -> KInner:
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

    def instantiate_cell_vars(self, term: KInner) -> KInner:
        def _cell_vars_to_labels(_kast: KInner) -> KInner:
            if type(_kast) is KApply and _kast.is_cell:
                production = self.production_for_klabel(_kast.label)
                production_arity = [prod_item.sort for prod_item in production.items if type(prod_item) is KNonTerminal]
                new_args = []
                for sort, arg in zip(production_arity, _kast.args):
                    if sort.name.endswith('Cell') and type(arg) is KVariable:
                        new_args.append(self.empty_config(sort))
                    else:
                        new_args.append(arg)
                return KApply(_kast.label, new_args)
            return _kast

        return bottom_up(_cell_vars_to_labels, term)

    def init_config(self, sort: KSort) -> KInner:
        if sort not in self._init_config:
            self._init_config[sort] = self._compute_init_config(sort)
        return self._init_config[sort]

    def _compute_init_config(self, sort: KSort) -> KInner:

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


def read_kast_definition(path: Union[str, PathLike]) -> KDefinition:
    with open(path, 'r') as _f:
        return KDefinition.from_dict(json.loads(_f.read())['term'])
