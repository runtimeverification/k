from dataclasses import dataclass
from functools import reduce
from itertools import chain
from typing import Dict, Iterator, List, Mapping, Optional, Tuple, TypeVar

from .kast import (
    KApply,
    KInner,
    KRewrite,
    KSequence,
    KToken,
    KVariable,
    bottom_up,
    flattenLabel,
)
from .prelude import boolToken, mlAnd
from .utils import FrozenDict

K = TypeVar('K')
V = TypeVar('V')


@dataclass(frozen=True)
class Subst(Mapping[str, KInner]):
    _subst: FrozenDict[str, KInner]

    def __init__(self, subst: Mapping[str, KInner] = {}):
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
        def replace(term):
            if type(term) is KVariable and term.name in self:
                return self[term.name]
            return term

        return bottom_up(replace, term)

    def unapply(self, term: KInner) -> KInner:
        new_term = term
        for var_name in self:
            lhs = self[var_name]
            rhs = KVariable(var_name)
            new_term = replace_anywhere((lhs, rhs), new_term)
        return new_term


def extract_subst(term: KInner) -> Tuple[Subst, KInner]:

    def _subst_for_terms(term1: KInner, term2: KInner) -> Optional[Subst]:
        if type(term1) is KVariable and type(term2) not in {KToken, KVariable}:
            return Subst({term1.name: term2})
        if type(term2) is KVariable and type(term1) not in {KToken, KVariable}:
            return Subst({term2.name: term1})
        return None

    def _extract_subst(conjunct: KInner) -> Optional[Subst]:
        if type(conjunct) is KApply:
            if conjunct.label == '#Equals':
                subst = _subst_for_terms(conjunct.args[0], conjunct.args[1])

                if subst is not None:
                    return subst

                if conjunct.args[0] == boolToken(True) and type(conjunct.args[1]) is KApply and conjunct.args[1].label in {'_==K_', '_==Int_'}:
                    subst = _subst_for_terms(conjunct.args[1].args[0], conjunct.args[1].args[1])

                    if subst is not None:
                        return subst

        return None

    conjuncts = flattenLabel('#And', term)
    subst = Subst()
    rem_conjuncts: List[KInner] = []

    for conjunct in conjuncts:
        new_subst = _extract_subst(conjunct)
        if new_subst is None:
            rem_conjuncts.append(conjunct)
        else:
            subst = subst.compose(new_subst)

    return subst, mlAnd(rem_conjuncts)


def match(pattern: KInner, term: KInner) -> Optional[Subst]:
    """Perform syntactic pattern matching and return the substitution.

    -   Input: a pattern and a term.
    -   Output: substitution instantiating the pattern to the term.
    """

    # TODO simplify
    def _match(pattern: KInner, term: KInner) -> Optional[Dict[str, KInner]]:

        def combine_dicts(dict1: Optional[Mapping[K, V]], dict2: Optional[Mapping[K, V]]) -> Optional[Dict[K, V]]:
            if dict1 is None:
                return None

            if dict2 is None:
                return None

            intersecting_keys = (key for key in dict1 if key in dict2)
            if any(dict1[key] != dict2[key] for key in intersecting_keys):
                return None

            return {**dict1, **dict2}

        def combine(*dicts: Optional[Mapping[K, V]]) -> Optional[Dict[K, V]]:
            unit: Optional[Dict[K, V]] = {}
            return reduce(combine_dicts, dicts, unit)

        subst: Optional[Dict[str, KInner]] = {}
        if type(pattern) is KVariable:
            return {pattern.name: term}
        if type(pattern) is KToken and type(term) is KToken:
            return {} if pattern.token == term.token else None
        if type(pattern) is KApply and type(term) is KApply \
                and pattern.label == term.label and pattern.arity == term.arity:
            for patternArg, kastArg in zip(pattern.args, term.args):
                argSubst = _match(patternArg, kastArg)
                subst = combine(subst, argSubst)
                if subst is None:
                    return None
            return subst
        if type(pattern) is KRewrite and type(term) is KRewrite:
            lhsSubst = _match(pattern.lhs, term.lhs)
            rhsSubst = _match(pattern.rhs, term.rhs)
            return combine(lhsSubst, rhsSubst)
        if type(pattern) is KSequence and type(term) is KSequence and pattern.arity == term.arity:
            for (patternItem, substItem) in zip(pattern.items, term.items):
                itemSubst = _match(patternItem, substItem)
                subst = combine(subst, itemSubst)
                if subst is None:
                    return None
            return subst
        return None

    subst = _match(pattern, term)
    return Subst(subst) if subst is not None else None


def rewrite(rule: Tuple[KInner, KInner], term: KInner) -> KInner:
    """
    Rewrite a given term at the top with the supplied rule.

    :param rule: A rewrite rule of the form (lhs, rhs).
    :param term: Term to rewrite.
    :return: The term with the rewrite applied once at the top.
    """
    lhs, rhs = rule
    subst = match(lhs, term)
    if subst is not None:
        return subst(rhs)
    return term


def rewrite_anywhere(rule: Tuple[KInner, KInner], term: KInner) -> KInner:
    """
    Attempt rewriting once at every position in a term bottom-up.

    :param rule: A rewrite rule of the form (lhs, rhs).
    :param term: Term to rewrite.
    :return: The term with rewrites applied at every node once starting from the bottom.
    """
    return bottom_up(lambda t: rewrite(rule, t), term)


def replace(rule: Tuple[KInner, KInner], term: KInner) -> KInner:
    lhs, rhs = rule
    if lhs == term:
        return rhs
    return term


def replace_anywhere(rule: Tuple[KInner, KInner], term: KInner) -> KInner:
    return bottom_up(lambda t: replace(rule, t), term)
