from dataclasses import dataclass
from functools import cached_property
from itertools import chain
from typing import Iterable, Optional, Tuple

from .kast import TOP, KApply, KInner, Subst, flattenLabel
from .kastManip import match, splitConfigAndConstraints
from .prelude import mlAnd, mlImplies
from .utils import unique


@dataclass(frozen=True)
class CTerm:
    config: KInner  # TODO Optional?
    constraints: Tuple[KInner, ...]

    def __init__(self, term: KInner) -> None:
        config, constraint = splitConfigAndConstraints(term)
        constraints = CTerm._normalize_constraints(flattenLabel('#And', constraint))
        object.__setattr__(self, 'config', config)
        object.__setattr__(self, 'constraints', constraints)

    @staticmethod
    def _normalize_constraints(constraints: Iterable[KInner]) -> Tuple[KInner, ...]:
        constraints = unique(constraints)
        constraints = (constraint for constraint in constraints if not CTerm._is_spurious_constraint(constraint))
        constraints = sorted(constraints, key=CTerm._constraint_sort_key)
        return tuple(constraints)

    @staticmethod
    def _is_spurious_constraint(term: KInner) -> bool:
        return type(term) is KApply and term.label == '#Equals' and term.args[0] == term.args[1]

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

    def match(self, term: 'CTerm') -> Optional[Subst]:
        match_res = self.match_with_constraint(term)

        if not match_res:
            return None

        subst, condition = match_res

        if condition != TOP:
            return None

        return subst

    def match_with_constraint(self, term: 'CTerm') -> Optional[Tuple[Subst, KInner]]:
        subst = match(pattern=self.config, term=term.config)

        if subst is None:
            return None

        constraint = self._ml_impl(term.constraints, map(subst, self.constraints))

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
