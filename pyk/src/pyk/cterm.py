from dataclasses import dataclass
from functools import cached_property
from itertools import chain
from typing import Iterable, Optional, Tuple

from .kast import KApply, KInner, Subst, flattenLabel
from .prelude import Sorts, mlAnd, mlImplies, mlTop
from .utils import unique


@dataclass(frozen=True)
class CTerm:
    config: KInner  # TODO Optional?
    constraints: Tuple[KInner, ...]

    def __init__(self, term: KInner) -> None:
        config, constraint = CTerm._split_config_and_constraints(term)
        constraints = CTerm._normalize_constraints(flattenLabel('#And', constraint))
        object.__setattr__(self, 'config', config)
        object.__setattr__(self, 'constraints', constraints)

    @staticmethod
    def _split_config_and_constraints(kast: KInner) -> Tuple[KInner, KInner]:
        conjuncts = flattenLabel('#And', kast)
        term = None
        constraints = []
        for c in conjuncts:
            if type(c) is KApply and c.is_cell:
                term = c
            else:
                constraints.append(c)
        if not term:
            raise ValueError(f'Could not find configuration for: {kast}')
        return (term, mlAnd(constraints, Sorts.GENERATED_TOP_CELL))

    @staticmethod
    def _normalize_constraints(constraints: Iterable[KInner]) -> Tuple[KInner, ...]:
        constraints = unique(constraints)
        constraints = (constraint for constraint in constraints if not CTerm._is_spurious_constraint(constraint))
        constraints = sorted(constraints, key=CTerm._constraint_sort_key)
        return tuple(constraints)

    @staticmethod
    def _is_spurious_constraint(term: KInner) -> bool:
        return type(term) is KApply and term.label.name == '#Equals' and term.args[0] == term.args[1]

    @staticmethod
    def _constraint_sort_key(term: KInner) -> Tuple[int, str]:
        term_str = str(term)
        return (len(term_str), term_str)

    def __iter__(self):
        return chain([self.config], self.constraints)

    @cached_property
    def term(self) -> KInner:
        return mlAnd(self, Sorts.GENERATED_TOP_CELL)

    @property
    def hash(self) -> str:
        return self.term.hash

    def match(self, cterm: 'CTerm') -> Optional[Subst]:
        match_res = self.match_with_constraint(cterm)

        if not match_res:
            return None

        subst, condition = match_res

        if condition != mlTop(Sorts.GENERATED_TOP_CELL):
            return None

        return subst

    def match_with_constraint(self, cterm: 'CTerm') -> Optional[Tuple[Subst, KInner]]:
        subst = self.config.match(cterm.config)

        if subst is None:
            return None

        constraint = self._ml_impl(cterm.constraints, map(subst, self.constraints))

        return subst, constraint

    @staticmethod
    def _ml_impl(antecedents: Iterable[KInner], consequents: Iterable[KInner]) -> KInner:
        antecedent = mlAnd(unique(antecedents), Sorts.GENERATED_TOP_CELL)
        consequent = mlAnd(unique(term for term in consequents if term not in set(antecedents)), Sorts.GENERATED_TOP_CELL)

        if mlTop(Sorts.GENERATED_TOP_CELL) in {antecedent, consequent}:
            return consequent

        return mlImplies(antecedent, consequent, Sorts.GENERATED_TOP_CELL)

    def add_constraint(self, new_constraint: KInner) -> 'CTerm':
        return CTerm(mlAnd([self.config, new_constraint] + list(self.constraints), Sorts.GENERATED_TOP_CELL))
