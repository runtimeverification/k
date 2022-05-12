from dataclasses import dataclass
from functools import cached_property
from itertools import chain
from typing import Iterable, Optional, Tuple

from .kast import TOP, KInner, flattenLabel
from .kastManip import match, splitConfigAndConstraints
from .prelude import mlAnd, mlImplies
from .rewrite import Subst


@dataclass(frozen=True)
class CTerm:
    config: KInner  # TODO Optional?
    constraints: Tuple[KInner, ...]

    def __init__(self, term: KInner) -> None:
        config, constraint = splitConfigAndConstraints(term)
        constraints = tuple(sorted(set(flattenLabel('#And', constraint)), key=self._constraint_sort_key))
        object.__setattr__(self, 'config', config)
        object.__setattr__(self, 'constraints', constraints)

    @staticmethod
    def _constraint_sort_key(term: KInner) -> Tuple[int, str]:
        term_str = str(term)
        return (len(term_str), term_str)

    def __iter__(self):
        return chain([self.config], self.constraints)

    @cached_property
    def term(self) -> KInner:
        return mlAnd(self)

    @property
    def hash(self) -> str:
        return self.term.hash

    def match(self, pattern: 'CTerm') -> Optional[Subst]:
        match_res = self.match_with_constraint(pattern)

        if not match_res:
            return None

        subst, condition = match_res

        if condition != TOP:
            return None

        return subst

    def match_with_constraint(self, pattern: 'CTerm') -> Optional[Tuple[Subst, KInner]]:
        subst = match(pattern=pattern.config, term=self.config)

        if subst is None:
            return None

        constraint = self._ml_impl(self.constraints, map(subst, pattern.constraints))

        return subst, constraint

    @staticmethod
    def _ml_impl(antecedents: Iterable[KInner], consequents: Iterable[KInner]) -> KInner:
        antecedents = set(antecedents)

        antecedent = mlAnd(antecedents)
        consequent = mlAnd(set(term for term in consequents if term not in antecedents))

        if antecedent == TOP:
            return consequent

        if consequent == TOP:
            return TOP

        return mlImplies(antecedent, consequent)
