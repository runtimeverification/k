from __future__ import annotations

import json
import logging
from abc import abstractmethod
from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass
from enum import Enum
from functools import cached_property
from typing import TYPE_CHECKING, final

from ..prelude.kbool import TRUE
from ..prelude.ml import ML_QUANTIFIERS
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
    bottom_up_with_summary,
    top_down,
)
from .kast import EMPTY_ATT, KAst, KAtt, WithKAtt, kast_term

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping
    from dataclasses import InitVar
    from os import PathLike
    from typing import Any, Final, TypeVar

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
    def from_dict(cls: type[KOuter], d: Mapping[str, Any]) -> KOuter:
        node = d['node']
        if node in KOuter._OUTER_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected "node" value in: {KOuter._OUTER_NODES}, got: {node}')


class KProductionItem(KOuter):
    _PRODUCTION_ITEM_NODES: Final = {'KTerminal', 'KRegexTerminal', 'KNonTerminal'}

    @classmethod
    @abstractmethod
    def from_dict(cls: type[KProductionItem], d: Mapping[str, Any]) -> KProductionItem:
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
    def from_dict(cls: type[KSentence], d: Mapping[str, Any]) -> KSentence:
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
    def from_dict(cls: type[KTerminal], d: Mapping[str, Any]) -> KTerminal:
        cls._check_node(d)
        return KTerminal(value=d['value'])

    def to_dict(self) -> dict[str, Any]:
        return {'node': 'KTerminal', 'value': self.value}

    def let(self, *, value: str | None = None) -> KTerminal:
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
    def from_dict(cls: type[KRegexTerminal], d: Mapping[str, Any]) -> KRegexTerminal:
        cls._check_node(d)
        return KRegexTerminal(
            regex=d['regex'],
            precede_regex=d['precedeRegex'],
            follow_regex=d['followRegex'],
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KRegexTerminal',
            'regex': self.regex,
            'precedeRegex': self.precede_regex,
            'followRegex': self.follow_regex,
        }

    def let(
        self, *, regex: str | None = None, precede_regex: str | None = None, follow_regex: str | None = None
    ) -> KRegexTerminal:
        regex = regex if regex is not None else self.regex
        precede_regex = precede_regex if precede_regex is not None else self.precede_regex
        follow_regex = follow_regex if follow_regex is not None else self.follow_regex
        return KRegexTerminal(regex=regex, precede_regex=precede_regex, follow_regex=follow_regex)


@final
@dataclass(frozen=True)
class KNonTerminal(KProductionItem):
    sort: KSort
    name: str | None

    def __init__(self, sort: KSort, name: str | None = None):
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'name', name)

    @classmethod
    def from_dict(cls: type[KNonTerminal], d: Mapping[str, Any]) -> KNonTerminal:
        cls._check_node(d)
        name = d['name'] if 'name' in d else None
        return KNonTerminal(sort=KSort.from_dict(d['sort']), name=name)

    def to_dict(self) -> dict[str, Any]:
        d = {'node': 'KNonTerminal', 'sort': self.sort.to_dict()}
        if self.name is not None:
            d['name'] = self.name
        return d

    def let(self, *, sort: KSort | None = None, name: str | None = None) -> KNonTerminal:
        sort = sort or self.sort
        name = name or self.name
        return KNonTerminal(sort=sort, name=name)


@final
@dataclass(frozen=True)
class KProduction(KSentence):
    # TODO Order in Java implementation: klabel, params, sort, items, att
    sort: KSort
    items: tuple[KProductionItem, ...]
    params: tuple[KSort, ...]
    klabel: KLabel | None
    att: KAtt

    def __init__(
        self,
        sort: str | KSort,
        items: Iterable[KProductionItem] = (),
        params: Iterable[str | KSort] = (),
        klabel: str | KLabel | None = None,
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
    def argument_sorts(self) -> list[KSort]:
        return [knt.sort for knt in self.items if type(knt) is KNonTerminal]

    @classmethod
    def from_dict(cls: type[KProduction], d: Mapping[str, Any]) -> KProduction:
        cls._check_node(d)
        return KProduction(
            sort=KSort.from_dict(d['sort']),
            items=(KProductionItem.from_dict(item) for item in d['productionItems']),
            params=(KSort.from_dict(param) for param in d['params']),
            klabel=KLabel.from_dict(d['klabel']) if d.get('klabel') else None,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
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
        sort: str | KSort | None = None,
        items: Iterable[KProductionItem] | None = None,
        params: Iterable[str | KSort] | None = None,
        klabel: str | KLabel | None = None,
        att: KAtt | None = None,
    ) -> KProduction:
        sort = sort if sort is not None else self.sort
        items = items if items is not None else self.items
        params = params if params is not None else self.params
        klabel = klabel if klabel is not None else self.klabel  # TODO figure out a way to set klabel to None
        att = att if att is not None else self.att
        return KProduction(sort=sort, items=items, params=params, klabel=klabel, att=att)

    def let_att(self, att: KAtt) -> KProduction:
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSyntaxSort(KSentence):
    sort: KSort
    params: tuple[KSort, ...]
    att: KAtt

    def __init__(self, sort: KSort, params: Iterable[str | KSort] = (), att: KAtt = EMPTY_ATT):
        params = tuple(KSort(param) if type(param) is str else param for param in params)
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'params', params)
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: type[KSyntaxSort], d: Mapping[str, Any]) -> KSyntaxSort:
        cls._check_node(d)
        return KSyntaxSort(
            sort=KSort.from_dict(d['sort']),
            params=(KSort.from_dict(param) for param in d['params']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KSyntaxSort',
            'sort': self.sort.to_dict(),
            'params': [param.to_dict() for param in self.params],
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        sort: KSort | None = None,
        params: Iterable[str | KSort] | None = None,
        att: KAtt | None = None,
    ) -> KSyntaxSort:
        sort = sort or self.sort
        params = params if params is not None else self.params
        att = att if att is not None else self.att
        return KSyntaxSort(sort=sort, params=params, att=att)

    def let_att(self, att: KAtt) -> KSyntaxSort:
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
    def from_dict(cls: type[KSortSynonym], d: Mapping[str, Any]) -> KSortSynonym:
        cls._check_node(d)
        return KSortSynonym(
            new_sort=KSort.from_dict(d['newSort']),
            old_sort=KSort.from_dict(d['oldSort']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KSortSynonym',
            'newSort': self.new_sort.to_dict(),
            'oldSort': self.old_sort.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(
        self, *, old_sort: KSort | None = None, new_sort: KSort | None = None, att: KAtt | None = None
    ) -> KSortSynonym:
        new_sort = new_sort or self.new_sort
        old_sort = old_sort or self.old_sort
        att = att if att is not None else self.att
        return KSortSynonym(new_sort=new_sort, old_sort=old_sort, att=att)

    def let_att(self, att: KAtt) -> KSortSynonym:
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
    def from_dict(cls: type[KSyntaxLexical], d: Mapping[str, Any]) -> KSyntaxLexical:
        cls._check_node(d)
        return KSyntaxLexical(
            name=d['name'],
            regex=d['regex'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KSyntaxLexcial',
            'name': self.name,
            'regex': self.regex,
            'att': self.att.to_dict(),
        }

    def let(self, *, name: str | None = None, regex: str | None = None, att: KAtt | None = None) -> KSyntaxLexical:
        name = name if name is not None else self.name
        regex = regex if regex is not None else self.regex
        att = att if att is not None else self.att
        return KSyntaxLexical(name=name, regex=regex, att=att)

    def let_att(self, att: KAtt) -> KSyntaxLexical:
        return self.let(att=att)


class KAssoc(Enum):
    LEFT = 'Left'
    RIGHT = 'Right'
    NON_ASSOC = 'NonAssoc'


@final
@dataclass(frozen=True)
class KSyntaxAssociativity(KSentence):
    assoc: KAssoc
    tags: frozenset[str]
    att: KAtt

    def __init__(self, assoc: KAssoc, tags: Iterable[str] = frozenset(), att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'assoc', assoc)
        object.__setattr__(self, 'tags', frozenset(tags))
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: type[KSyntaxAssociativity], d: Mapping[str, Any]) -> KSyntaxAssociativity:
        cls._check_node(d)
        return KSyntaxAssociativity(
            assoc=KAssoc(d['assoc']),
            tags=d['tags'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KSyntaxAssociativity',
            'assoc': self.assoc.value,
            'tags': list(self.tags),
            'att': self.att.to_dict(),
        }

    def let(
        self, *, assoc: KAssoc | None = None, tags: Iterable[str] | None = None, att: KAtt | None = None
    ) -> KSyntaxAssociativity:
        assoc = assoc or self.assoc
        tags = tags if tags is not None else self.tags
        att = att if att is not None else self.att
        return KSyntaxAssociativity(assoc=assoc, tags=tags, att=att)

    def let_att(self, att: KAtt) -> KSyntaxAssociativity:
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KSyntaxPriority(KSentence):
    priorities: tuple[frozenset[str], ...]
    att: KAtt

    def __init__(self, priorities: Iterable[Iterable[str]] = (), att: KAtt = EMPTY_ATT):
        object.__setattr__(self, 'priorities', tuple(frozenset(group) for group in priorities))
        object.__setattr__(self, 'att', att)

    @classmethod
    def from_dict(cls: type[KSyntaxPriority], d: Mapping[str, Any]) -> KSyntaxPriority:
        cls._check_node(d)
        return KSyntaxPriority(
            priorities=d['priorities'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KSyntaxPriority',
            'priorities': [list(group) for group in self.priorities],
            'att': self.att.to_dict(),
        }

    def let(self, *, priorities: Iterable[Iterable[str]] | None = None, att: KAtt | None = None) -> KSyntaxPriority:
        priorities = priorities if priorities is not None else self.priorities
        att = att if att is not None else self.att
        return KSyntaxPriority(priorities=priorities, att=att)

    def let_att(self, att: KAtt) -> KSyntaxPriority:
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
    def from_dict(cls: type[KBubble], d: Mapping[str, Any]) -> KBubble:
        cls._check_node(d)
        return KBubble(
            sentence_type=d['sentenceType'],
            content=d['content'],
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KBubble',
            'sentenceType': self.sentence_type,
            'content': self.content,
            'att': self.att.to_dict(),
        }

    def let(self, *, sentence_type: str | None = None, content: str | None = None, att: KAtt | None = None) -> KBubble:
        sentence_type = sentence_type if sentence_type is not None else self.sentence_type
        content = content if content is not None else self.content
        att = att if att is not None else self.att
        return KBubble(sentence_type=sentence_type, content=content, att=att)

    def let_att(self, att: KAtt) -> KBubble:
        return self.let(att=att)


class KRuleLike(KSentence):
    body: KInner
    requires: KInner
    ensures: KInner

    _RULE_LIKE_NODES: Final = {'KRule', 'KClaim'}

    @classmethod
    @abstractmethod
    def from_dict(cls: type[KRuleLike], d: Mapping[str, Any]) -> KRuleLike:
        node = d['node']
        if node in KRuleLike._RULE_LIKE_NODES:
            return globals()[node].from_dict(d)

        raise ValueError(f'Expected "node" value in: {KRuleLike._RULE_LIKE_NODES}, got: {node}')

    @abstractmethod
    def let(
        self: RL,
        *,
        body: KInner | None = None,
        requires: KInner | None = None,
        ensures: KInner | None = None,
        att: KAtt | None = None,
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
    def from_dict(cls: type[KRule], d: Mapping[str, Any]) -> KRule:
        cls._check_node(d)
        return KRule(
            body=KInner.from_dict(d['body']),
            requires=KInner.from_dict(d['requires']) if d.get('requires') else TRUE,
            ensures=KInner.from_dict(d['ensures']) if d.get('ensures') else TRUE,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
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
        body: KInner | None = None,
        requires: KInner | None = None,
        ensures: KInner | None = None,
        att: KAtt | None = None,
    ) -> KRule:
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        ensures = ensures if ensures is not None else self.ensures
        att = att if att is not None else self.att
        return KRule(body=body, requires=requires, ensures=ensures, att=att)

    def let_att(self, att: KAtt) -> KRule:
        return self.let(att=att)

    @property
    def priority(self) -> int:
        return self.att.get('priority', 200 if 'owise' in self.att else 50)


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
    def from_dict(cls: type[KClaim], d: Mapping[str, Any]) -> KClaim:
        cls._check_node(d)
        return KClaim(
            body=KInner.from_dict(d['body']),
            requires=KInner.from_dict(d['requires']) if d.get('requires') else TRUE,
            ensures=KInner.from_dict(d['ensures']) if d.get('ensures') else TRUE,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
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
        body: KInner | None = None,
        requires: KInner | None = None,
        ensures: KInner | None = None,
        att: KAtt | None = None,
    ) -> KClaim:
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        ensures = ensures if ensures is not None else self.ensures
        att = att if att is not None else self.att
        return KClaim(body=body, requires=requires, ensures=ensures, att=att)

    def let_att(self, att: KAtt) -> KClaim:
        return self.let(att=att)

    @property
    def is_circularity(self) -> bool:
        return 'circularity' in self.att.atts

    @property
    def dependencies(self) -> list[str]:
        deps = self.att.atts.get('depends', default=None)
        if deps is None:
            return []
        return [x.strip() for x in deps.split(',')]


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
    def from_dict(cls: type[KContext], d: Mapping[str, Any]) -> KContext:
        cls._check_node(d)
        return KContext(
            body=KInner.from_dict(d['body']),
            requires=KInner.from_dict(d['requires']) if d.get('requires') else TRUE,
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KContext',
            'body': self.body.to_dict(),
            'requires': self.requires.to_dict(),
            'att': self.att.to_dict(),
        }

    def let(self, *, body: KInner | None = None, requires: KInner | None = None, att: KAtt | None = None) -> KContext:
        body = body if body is not None else self.body
        requires = requires if requires is not None else self.requires
        att = att if att is not None else self.att
        return KContext(body=body, requires=requires, att=att)

    def let_att(self, att: KAtt) -> KContext:
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
    def from_dict(cls: type[KImport], d: Mapping[str, Any]) -> KImport:
        cls._check_node(d)
        return KImport(name=d['name'], public=d['isPublic'])

    def to_dict(self) -> dict[str, Any]:
        return {'node': 'KImport', 'name': self.name, 'isPublic': self.public}

    def let(self, *, name: str | None = None, public: bool | None = None) -> KImport:
        name = name if name is not None else self.name
        public = public if public is not None else self.public
        return KImport(name=name, public=public)


@final
@dataclass(frozen=True)
class KFlatModule(KOuter, WithKAtt, Iterable[KSentence]):
    name: str
    sentences: tuple[KSentence, ...]
    imports: tuple[KImport, ...]
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
    def productions(self) -> tuple[KProduction, ...]:
        return tuple(sentence for sentence in self if type(sentence) is KProduction)

    @cached_property
    def syntax_productions(self) -> tuple[KProduction, ...]:
        return tuple(prod for prod in self.productions if prod.klabel)

    @cached_property
    def functions(self) -> tuple[KProduction, ...]:
        return tuple(prod for prod in self.syntax_productions if self._is_function(prod))

    @cached_property
    def constructors(self) -> tuple[KProduction, ...]:
        return tuple(prod for prod in self.syntax_productions if not self._is_function(prod))

    @cached_property
    def cell_collection_productions(self) -> tuple[KProduction, ...]:
        return tuple(prod for prod in self.syntax_productions if 'cellCollection' in prod.att)

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
    def rules(self) -> tuple[KRule, ...]:
        return tuple(sentence for sentence in self if type(sentence) is KRule)

    @cached_property
    def claims(self) -> tuple[KClaim, ...]:
        return tuple(sentence for sentence in self if type(sentence) is KClaim)

    @classmethod
    def from_dict(cls: type[KFlatModule], d: Mapping[str, Any]) -> KFlatModule:
        cls._check_node(d)
        return KFlatModule(
            name=d['name'],
            sentences=(KSentence.from_dict(sentence) for sentence in d['localSentences']),
            imports=(KImport.from_dict(imp) for imp in d['imports']),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
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
        name: str | None = None,
        sentences: Iterable[KSentence] | None = None,
        imports: Iterable[KImport] | None = None,
        att: KAtt | None = None,
    ) -> KFlatModule:
        name = name if name is not None else self.name
        sentences = sentences if sentences is not None else self.sentences
        imports = imports if imports is not None else self.imports
        att = att if att is not None else self.att
        return KFlatModule(name=name, imports=imports, sentences=sentences, att=att)

    def let_att(self, att: KAtt) -> KFlatModule:
        return self.let(att=att)


@final
@dataclass(frozen=True)
class KFlatModuleList(KOuter):
    main_module: str
    modules: tuple[KFlatModule, ...]

    def __init__(self, main_module: str, modules: Iterable[KFlatModule]):
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, 'modules', tuple(modules))

    @classmethod
    def from_dict(cls: type[KFlatModuleList], d: Mapping[str, Any]) -> KFlatModuleList:
        cls._check_node(d)
        return KFlatModuleList(main_module=d['mainModule'], modules=(KFlatModule.from_dict(kfm) for kfm in d['term']))

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KFlatModuleList',
            'mainModule': self.main_module,
            'term': [mod.to_dict() for mod in self.modules],
        }

    def let(self, *, main_module: str | None = None, modules: Iterable[KFlatModule] | None = None) -> KFlatModuleList:
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
    def from_dict(cls: type[KRequire], d: Mapping[str, Any]) -> KRequire:
        cls._check_node(d)
        return KRequire(require=d['require'])

    def to_dict(self) -> dict[str, Any]:
        return {'node': 'KRequire', 'require': self.require}

    def let(self, *, require: str | None = None) -> KRequire:
        require = require if require is not None else self.require
        return KRequire(require=require)


@final
@dataclass(frozen=True)
class KDefinition(KOuter, WithKAtt, Iterable[KFlatModule]):
    main_module_name: str
    all_modules: tuple[KFlatModule, ...]
    requires: tuple[KRequire, ...]
    att: KAtt

    main_module: InitVar[KFlatModule]

    _production_for_klabel: dict[KLabel, KProduction]
    _subsorts: dict[KSort, list[KSort]]
    _init_config: dict[KSort, KInner]
    _empty_config: dict[KSort, KInner]

    def __init__(
        self,
        main_module_name: str,
        all_modules: Iterable[KFlatModule],
        requires: Iterable[KRequire] = (),
        att: KAtt = EMPTY_ATT,
    ):
        all_modules = tuple(all_modules)
        main_modules = [module for module in all_modules if module.name == main_module_name]

        if not main_modules:
            raise ValueError(f'Module not found: {main_module_name}')
        if len(main_modules) > 1:
            raise ValueError(f'Module is not unique: {main_module_name}')

        main_module = main_modules[0]

        object.__setattr__(self, 'main_module_name', main_module_name)
        object.__setattr__(self, 'all_modules', tuple(all_modules))
        object.__setattr__(self, 'requires', tuple(requires))
        object.__setattr__(self, 'att', att)
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, '_production_for_klabel', {})
        object.__setattr__(self, '_subsorts', {})
        object.__setattr__(self, '_init_config', {})
        object.__setattr__(self, '_empty_config', {})

    def __iter__(self) -> Iterator[KFlatModule]:
        return iter(self.all_modules)

    @classmethod
    def from_dict(cls: type[KDefinition], d: Mapping[str, Any]) -> KDefinition:
        cls._check_node(d)
        return KDefinition(
            main_module_name=d['mainModule'],
            all_modules=(KFlatModule.from_dict(module) for module in d['modules']),
            requires=(KRequire.from_dict(require) for require in d['requires']) if d.get('requires') else (),
            att=KAtt.from_dict(d['att']) if d.get('att') else EMPTY_ATT,
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'node': 'KDefinition',
            'mainModule': self.main_module_name,
            'modules': [module.to_dict() for module in self.all_modules],
            'requires': [require.to_dict() for require in self.requires],
            'att': self.att.to_dict(),
        }

    def let(
        self,
        *,
        main_module_name: str | None = None,
        all_modules: Iterable[KFlatModule] | None = None,
        requires: Iterable[KRequire] | None = None,
        att: KAtt | None = None,
    ) -> KDefinition:
        main_module_name = main_module_name if main_module_name is not None else self.main_module_name
        all_modules = all_modules if all_modules is not None else self.all_modules
        requires = requires if requires is not None else self.requires
        att = att if att is not None else self.att
        return KDefinition(main_module_name=main_module_name, all_modules=all_modules, requires=requires, att=att)

    def let_att(self, att: KAtt) -> KDefinition:
        return self.let(att=att)

    @cached_property
    def all_module_names(self) -> tuple[str, ...]:
        return tuple(module.name for module in self.all_modules)

    @cached_property
    def module_names(self) -> tuple[str, ...]:
        module_names = [self.main_module_name]
        seen_modules = []
        while len(module_names) > 0:
            mname = module_names.pop(0)
            if mname not in seen_modules:
                seen_modules.append(mname)
                module_names.extend([i.name for i in self.all_modules_dict[mname].imports])
        return tuple(seen_modules)

    @cached_property
    def all_modules_dict(self) -> dict[str, KFlatModule]:
        return {m.name: m for m in self.all_modules}

    @cached_property
    def modules(self) -> tuple[KFlatModule, ...]:
        return tuple(self.all_modules_dict[mname] for mname in self.module_names)

    @cached_property
    def productions(self) -> tuple[KProduction, ...]:
        return tuple(prod for module in self.modules for prod in module.productions)

    @cached_property
    def syntax_productions(self) -> tuple[KProduction, ...]:
        return tuple(prod for module in self.modules for prod in module.syntax_productions)

    @cached_property
    def functions(self) -> tuple[KProduction, ...]:
        return tuple(func for module in self.modules for func in module.functions)

    @cached_property
    def constructors(self) -> tuple[KProduction, ...]:
        return tuple(ctor for module in self.modules for ctor in module.constructors)

    @cached_property
    def cell_collection_productions(self) -> tuple[KProduction, ...]:
        return tuple(prod for module in self.modules for prod in module.cell_collection_productions)

    @cached_property
    def rules(self) -> tuple[KRule, ...]:
        return tuple(rule for module in self.modules for rule in module.rules)

    @cached_property
    def alias_rules(self) -> tuple[KRule, ...]:
        return tuple(rule for rule in self.rules if 'alias' in rule.att)

    @cached_property
    def macro_rules(self) -> tuple[KRule, ...]:
        return tuple(rule for rule in self.rules if 'macro' in rule.att) + self.alias_rules

    @cached_property
    def semantic_rules(self) -> tuple[KRule, ...]:
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
                _LOGGER.warning(
                    f'Discarding {len(prods) - len(_prods)} productions with `unparseAvoid` attribute for label: {klabel}'
                )
                prods = _prods
            # Automatically defined symbols like isInt may get multiple
            # definitions in different modules.
            _prods = list({prod.let_att(prod.att.drop_source()) for prod in prods})
            if len(_prods) < len(prods):
                _LOGGER.warning(f'Discarding {len(prods) - len(_prods)} equivalent productions')
                prods = _prods
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
        return self.all_modules_dict[name]

    def return_sort(self, label: KLabel) -> KSort:
        return self.production_for_klabel(label).sort

    def argument_sorts(self, label: KLabel) -> list[KSort]:
        return self.production_for_klabel(label).argument_sorts

    def subsorts(self, sort: KSort) -> list[KSort]:
        if sort not in self._subsorts:
            self._subsorts[sort] = self._compute_subsorts(sort)
        return self._subsorts[sort]

    def _compute_subsorts(self, sort: KSort) -> list[KSort]:
        _subsorts = []
        for prod in self.productions:
            if prod.sort == sort and len(prod.items) == 1 and type(prod.items[0]) is KNonTerminal:
                _subsort = prod.items[0].sort
                _subsorts.extend([_subsort] + self.subsorts(prod.items[0].sort))
        return list(set(_subsorts))

    def sort(self, kast: KInner) -> KSort | None:
        match kast:
            case KToken(_, sort) | KVariable(_, sort):
                return sort
            case KRewrite(lhs, rhs):
                sort = self.sort(lhs)
                return sort if sort == self.sort(rhs) else None
            case KSequence(_):
                return KSort('K')
            case KApply(label, _):
                prod = self.production_for_klabel(label)
                if prod.sort not in prod.params:
                    return prod.sort
                elif len(prod.params) == len(label.params):
                    param_dict: dict[KSort, KSort] = {}
                    for pparam, lparam in zip(prod.params, label.params, strict=True):
                        if pparam not in param_dict:
                            param_dict[pparam] = lparam
                        elif param_dict[pparam] != lparam:
                            return None
                    if prod.sort in param_dict and param_dict[prod.sort] not in prod.params:
                        return param_dict[prod.sort]
                return None
            case _:
                return None

    def sort_strict(self, kast: KInner) -> KSort:
        sort = self.sort(kast)
        if sort is None:
            raise ValueError(f'Could not determine sort of term: {kast}')
        return sort

    def greatest_common_subsort(self, sort1: KSort, sort2: KSort) -> KSort | None:
        if sort1 == sort2:
            return sort1
        if sort1 in self.subsorts(sort2):
            return sort1
        if sort2 in self.subsorts(sort1):
            return sort2
        return None

    # Sorts like Int cannot be injected directly into sort K so they are embedded in a KSequence.
    def add_ksequence_under_kequal(self, kast: KInner) -> KInner:
        def _add_ksequence_under_kequal(kast: KInner) -> KInner:
            if type(kast) is KApply and kast.label.name == '_==K_':
                return KApply('_==K_', [KSequence(arg) for arg in kast.args])
            else:
                return kast

        return top_down(_add_ksequence_under_kequal, kast)

    def sort_vars(self, kast: KInner, sort: KSort | None = None) -> KInner:
        if type(kast) is KVariable and kast.sort is None and sort is not None:
            return kast.let(sort=sort)

        def get_quantifier_variable(q: KApply) -> KVariable:
            if q.arity != 2:
                raise ValueError(f'Expected a quantifier to have 2 children, got {q.arity}.')
            var = q.args[0]
            if not isinstance(var, KVariable):
                raise ValueError(f"Expected a quantifier's first child to be a variable, got {type(var)}.")
            return var

        def merge_variables(
            term: KInner, occurrences_list: list[dict[str, list[KVariable]]]
        ) -> dict[str, list[KVariable]]:
            result: dict[str, list[KVariable]] = defaultdict(list)
            for occurrences in occurrences_list:
                assert isinstance(occurrences, dict), type(occurrences)
                for key, value in occurrences.items():
                    result[key] += value
            if isinstance(term, KVariable):
                result[term.name].append(term)
            elif isinstance(term, KApply):
                if term.label.name in ML_QUANTIFIERS:
                    var = get_quantifier_variable(term)
                    result[var.name].append(var)
            return result

        def add_var_to_subst(vname: str, vars: list[KVariable], subst: dict[str, KVariable]) -> None:
            vsorts = list(unique(v.sort for v in vars if v.sort is not None))
            if len(vsorts) > 0:
                vsort = vsorts[0]
                for s in vsorts[1:]:
                    _vsort = self.greatest_common_subsort(vsort, s)
                    if _vsort is None:
                        raise ValueError(f'Cannot compute greatest common subsort of {vname}: {(vsort, s)}')
                    vsort = _vsort
                subst[vname] = KVariable(vname, sort=vsort)

        def transform(
            term: KInner, child_variables: list[dict[str, list[KVariable]]]
        ) -> tuple[KInner, dict[str, list[KVariable]]]:
            occurrences = merge_variables(term, child_variables)

            if isinstance(term, KApply):
                if term.label.name in ML_QUANTIFIERS:
                    var = get_quantifier_variable(term)
                    subst: dict[str, KVariable] = {}
                    add_var_to_subst(var.name, occurrences[var.name], subst)
                    del occurrences[var.name]
                    return (Subst(subst)(term), occurrences)
                else:
                    prod = self.production_for_klabel(term.label)
                    if len(prod.params) == 0:
                        for t, a in zip(prod.argument_sorts, term.args, strict=True):
                            if type(a) is KVariable:
                                occurrences[a.name].append(a.let_sort(t))
            elif isinstance(term, KSequence) and term.arity > 0:
                for a in term.items[0:-1]:
                    if type(a) is KVariable:
                        occurrences[a.name].append(a.let_sort(KSort('KItem')))
                last_a = term.items[-1]
                if type(last_a) is KVariable:
                    occurrences[last_a.name].append(last_a.let_sort(KSort('K')))
            return (term, occurrences)

        (new_term, var_occurrences) = bottom_up_with_summary(transform, kast)

        subst: dict[str, KVariable] = {}
        for vname, occurrences in var_occurrences.items():
            add_var_to_subst(vname, occurrences, subst)

        return Subst(subst)(new_term)

    # Best-effort addition of sort parameters to klabels, context insensitive
    def add_sort_params(self, kast: KInner) -> KInner:
        def _add_sort_params(_k: KInner) -> KInner:
            if type(_k) is KApply:
                prod = self.production_for_klabel(_k.label)
                if len(_k.label.params) == 0 and len(prod.params) > 0:
                    sort_dict: dict[KSort, KSort] = {}
                    for psort, asort in zip(prod.argument_sorts, map(self.sort, _k.args), strict=True):
                        if asort is None:
                            _LOGGER.warning(
                                f'Failed to add sort parameter, unable to determine sort for argument in production: {(prod, psort, asort)}'
                            )
                            return _k
                        if psort in prod.params:
                            if psort in sort_dict and sort_dict[psort] != asort:
                                _LOGGER.warning(
                                    f'Failed to add sort parameter, sort mismatch between different occurances of sort parameter: {(prod, psort, sort_dict[psort], asort)}'
                                )
                                return _k
                            elif psort not in sort_dict:
                                sort_dict[psort] = asort
                    if all(p in sort_dict for p in prod.params):
                        return _k.let(label=KLabel(_k.label.name, [sort_dict[p] for p in prod.params]))
            return _k

        return bottom_up(_add_sort_params, kast)

    def add_cell_map_items(self, kast: KInner) -> KInner:
        # example:
        # syntax AccountCellMap [cellCollection, hook(MAP.Map)]
        # syntax AccountCellMap ::= AccountCellMap AccountCellMap [assoc, avoid, cellCollection, comm, element(AccountCellMapItem), function, hook(MAP.concat), unit(.AccountCellMap), wrapElement(<account>)]

        cell_wrappers = {}
        for ccp in self.cell_collection_productions:
            if 'element' in ccp.att and 'wrapElement' in ccp.att:
                cell_wrappers[ccp.att['wrapElement']] = ccp.att['element']

        def _wrap_elements(_k: KInner) -> KInner:
            if type(_k) is KApply and _k.label.name in cell_wrappers:
                return KApply(cell_wrappers[_k.label.name], [_k.args[0], _k])
            return _k

        # To ensure we don't get duplicate wrappers.
        _kast = self.remove_cell_map_items(kast)
        return bottom_up(_wrap_elements, _kast)

    def remove_cell_map_items(self, kast: KInner) -> KInner:
        # example:
        # syntax AccountCellMap [cellCollection, hook(MAP.Map)]
        # syntax AccountCellMap ::= AccountCellMap AccountCellMap [assoc, avoid, cellCollection, comm, element(AccountCellMapItem), function, hook(MAP.concat), unit(.AccountCellMap), wrapElement(<account>)]

        cell_wrappers = {}
        for ccp in self.cell_collection_productions:
            if 'element' in ccp.att and 'wrapElement' in ccp.att:
                cell_wrappers[ccp.att['element']] = ccp.att['wrapElement']

        def _wrap_elements(_k: KInner) -> KInner:
            if (
                type(_k) is KApply
                and _k.label.name in cell_wrappers
                and len(_k.args) == 2
                and type(_k.args[1]) is KApply
                and _k.args[1].label.name == cell_wrappers[_k.label.name]
            ):
                return _k.args[1]
            return _k

        return bottom_up(_wrap_elements, kast)

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
            args: list[KInner] = []
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
                for sort, arg in zip(production_arity, _kast.args, strict=True):
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
        old_init_config: KInner | None = None
        while init_config != old_init_config:
            old_init_config = init_config
            for rew in init_rewrites:
                assert type(rew) is KRewrite
                init_config = rew(init_config)

        init_config = top_down(_remove_config_var_lookups, init_config)

        return init_config


def read_kast_definition(path: str | PathLike) -> KDefinition:
    with open(path) as f:
        _LOGGER.info(f'Loading JSON definition: {path}')
        json_defn = json.load(f)
        _LOGGER.info(f'Converting JSON definition to Kast: {path}')
        return kast_term(json_defn, KDefinition)
