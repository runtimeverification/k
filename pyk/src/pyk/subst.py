from dataclasses import dataclass
from functools import reduce
from itertools import chain
from typing import Dict, Iterator, Mapping, Optional, TypeVar

from .kast import KApply, KInner, KRewrite, KSequence, KToken, KVariable
from .kastManip import bottom_up
from .utils import FrozenDict

K = TypeVar('K')
V = TypeVar('V')


@dataclass(frozen=True)
class Subst(Mapping[str, KInner]):
    _subst: FrozenDict[str, KInner]

    def __init__(self, subst: Mapping[str, KInner] = {}):
        object.__setattr__(self, '_subst', FrozenDict({k: v for k, v in subst.items() if type(v) is not KVariable or v.name != k}))

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

    def compose(self, other: 'Subst') -> 'Subst':
        from_other = ((k, self(v)) for k, v in other.items())
        from_self = ((k, v) for k, v in self.items() if k not in other)
        return Subst(dict(chain(from_other, from_self)))

    def apply(self, term: KInner) -> KInner:
        def replace(term):
            if type(term) is KVariable and term.name in self:
                return self[term.name]
            return term

        return bottom_up(replace, term)


def match(pattern: KInner, term: KInner) -> Optional[Subst]:
    """Perform syntactic pattern matching and return the substitution.

    -   Input: a pattern and a term.
    -   Output: substitution instantiating the pattern to the term.
    """

    # TODO simplify
    def _match(pattern: KInner, term: KInner) -> Optional[Dict[str, KInner]]:
        subst: Optional[Dict[str, KInner]] = {}
        if type(pattern) is KVariable:
            return {pattern.name: term}
        if type(pattern) is KToken and type(term) is KToken:
            return {} if pattern.token == term.token else None
        if type(pattern) is KApply and type(term) is KApply \
                and pattern.label == term.label and pattern.arity == term.arity:
            for patternArg, kastArg in zip(pattern.args, term.args):
                argSubst = _match(patternArg, kastArg)
                subst = combine_all(subst, argSubst)
                if subst is None:
                    return None
            return subst
        if type(pattern) is KRewrite and type(term) is KRewrite:
            lhsSubst = _match(pattern.lhs, term.lhs)
            rhsSubst = _match(pattern.rhs, term.rhs)
            return combine_all(lhsSubst, rhsSubst)
        if type(pattern) is KSequence and type(term) is KSequence and pattern.arity == term.arity:
            for (patternItem, substItem) in zip(pattern.items, term.items):
                itemSubst = _match(patternItem, substItem)
                subst = combine_all(subst, itemSubst)
                if subst is None:
                    return None
            return subst
        return None

    subst = _match(pattern, term)
    return Subst(subst) if subst is not None else None


def combine_dicts(dict1: Optional[Mapping[K, V]], dict2: Optional[Mapping[K, V]]) -> Optional[Dict[K, V]]:
    if dict1 is None:
        return None

    if dict2 is None:
        return None

    intersecting_keys = (key for key in dict1 if key in dict2)
    if any(dict1[key] != dict2[key] for key in intersecting_keys):
        return None

    return {**dict1, **dict2}


def combine_all(*dicts: Optional[Mapping[K, V]]) -> Optional[Dict[K, V]]:
    unit: Optional[Dict[K, V]] = {}
    return reduce(combine_dicts, dicts, unit)
