from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property
from itertools import chain
from typing import TYPE_CHECKING

from ..kast import KInner
from ..kast.inner import KApply, KRewrite, KToken, Subst, bottom_up
from ..kast.manip import (
    abstract_term_safely,
    build_claim,
    build_rule,
    flatten_label,
    free_vars,
    ml_pred_to_bool,
    normalize_constraints,
    push_down_rewrites,
    remove_useless_constraints,
    split_config_and_constraints,
    split_config_from,
)
from ..prelude.k import GENERATED_TOP_CELL
from ..prelude.kbool import andBool, orBool
from ..prelude.ml import is_bottom, is_top, mlAnd, mlBottom, mlEqualsTrue, mlImplies, mlTop
from ..utils import unique

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Any

    from ..kast.outer import KClaim, KDefinition, KRule


@dataclass(frozen=True, order=True)
class CTerm:
    """Represent a symbolic program state, obtained and manipulated using symbolic execution.

    Contains the data:
    - `config`: the _configuration_ (structural component of the state, potentially containing free variabls)
    - `constraints`: conditiions which limit/constraint the free variables from the `config`
    """

    config: KInner  # TODO Optional?
    constraints: tuple[KInner, ...]

    def __init__(self, config: KInner, constraints: Iterable[KInner] = ()) -> None:
        """Instantiate a given `CTerm`, performing basic sanity checks on the `config` and `constraints`."""
        if is_top(config, weak=True):
            config = mlTop()
            constraints = ()
        elif is_bottom(config, weak=True):
            config = mlBottom()
            constraints = ()
        else:
            self._check_config(config)
            constraints = self._normalize_constraints(constraints)
        object.__setattr__(self, 'config', config)
        object.__setattr__(self, 'constraints', constraints)

    @staticmethod
    def from_kast(kast: KInner) -> CTerm:
        """Interpret a given `KInner` as a `CTerm` by splitting the `config` and `constraints` (see `CTerm.kast`)."""
        if is_top(kast, weak=True):
            return CTerm.top()
        elif is_bottom(kast, weak=True):
            return CTerm.bottom()
        else:
            config, constraint = split_config_and_constraints(kast)
            constraints = flatten_label('#And', constraint)
            return CTerm(config, constraints)

    @staticmethod
    def from_dict(dct: dict[str, Any]) -> CTerm:
        """Deserialize a `CTerm` from its dictionary representation."""
        config = KInner.from_dict(dct['config'])
        constraints = [KInner.from_dict(c) for c in dct['constraints']]
        return CTerm(config, constraints)

    @staticmethod
    def top() -> CTerm:
        """Construct a `CTerm` representing all possible states."""
        return CTerm(mlTop(), ())

    @staticmethod
    def bottom() -> CTerm:
        """Construct a `CTerm` representing no possible states."""
        return CTerm(mlBottom(), ())

    @staticmethod
    def _check_config(config: KInner) -> None:
        if not isinstance(config, KApply) or not config.is_cell:
            raise ValueError(f'Expected cell label, found: {config}')

    @staticmethod
    def _normalize_constraints(constraints: Iterable[KInner]) -> tuple[KInner, ...]:
        constraints = sorted(normalize_constraints(constraints), key=CTerm._constraint_sort_key)
        return tuple(constraints)

    @property
    def is_bottom(self) -> bool:
        """Check if a given `CTerm` is trivially empty."""
        return is_bottom(self.config, weak=True) or any(is_bottom(cterm, weak=True) for cterm in self.constraints)

    @staticmethod
    def _constraint_sort_key(term: KInner) -> tuple[int, str]:
        term_str = str(term)
        return (len(term_str), term_str)

    def __iter__(self) -> Iterator[KInner]:
        """Return an iterator with the head being the `config` and the tail being the `constraints`."""
        return chain([self.config], self.constraints)

    def to_dict(self) -> dict[str, Any]:
        """Serialize a `CTerm` to dictionary representation."""
        return {
            'config': self.config.to_dict(),
            'constraints': [c.to_dict() for c in self.constraints],
        }

    @cached_property
    def kast(self) -> KInner:
        """Return the unstructured bare `KInner` representation of a `CTerm` (see `CTerm.from_kast`)."""
        return mlAnd(self, GENERATED_TOP_CELL)

    @cached_property
    def free_vars(self) -> frozenset[str]:
        """Return the set of free variable names contained in this `CTerm`."""
        return frozenset(free_vars(self.kast))

    @property
    def hash(self) -> str:
        """Unique hash representing the contents of this `CTerm`."""
        return self.kast.hash

    @cached_property
    def cells(self) -> Subst:
        """Return key-value store of the contents of each cell in the `config`."""
        _, subst = split_config_from(self.config)
        return Subst(subst)

    def cell(self, cell: str) -> KInner:
        """Access the contents of a named cell in the `config`, die on failure."""
        return self.cells[cell]

    def try_cell(self, cell: str) -> KInner | None:
        """Access the contents of a named cell in the `config`, return `None` on failure."""
        return self.cells.get(cell)

    def match(self, cterm: CTerm) -> Subst | None:
        """Find `Subst` instantiating this `CTerm` to the other, return `None` if no such `Subst` exists."""
        csubst = self.match_with_constraint(cterm)

        if not csubst:
            return None

        if csubst.constraint != mlTop(GENERATED_TOP_CELL):
            return None

        return csubst.subst

    def match_with_constraint(self, cterm: CTerm) -> CSubst | None:
        """Find `CSubst` instantiating this `CTerm` to the other, return `None` if no such `CSubst` exists."""
        subst = self.config.match(cterm.config)

        if subst is None:
            return None

        constraint = self._ml_impl(cterm.constraints, map(subst, self.constraints))

        return CSubst(subst=subst, constraints=[constraint])

    @staticmethod
    def _ml_impl(antecedents: Iterable[KInner], consequents: Iterable[KInner]) -> KInner:
        antecedent = mlAnd(unique(antecedents), GENERATED_TOP_CELL)
        consequent = mlAnd(unique(term for term in consequents if term not in set(antecedents)), GENERATED_TOP_CELL)

        if mlTop(GENERATED_TOP_CELL) in {antecedent, consequent}:
            return consequent

        return mlImplies(antecedent, consequent, GENERATED_TOP_CELL)

    def add_constraint(self, new_constraint: KInner) -> CTerm:
        """Return a new `CTerm` with the additional constraints."""
        return CTerm(self.config, [new_constraint] + list(self.constraints))

    def anti_unify(
        self, other: CTerm, keep_values: bool = False, kdef: KDefinition | None = None
    ) -> tuple[CTerm, CSubst, CSubst]:
        """Given two `CTerm` instances, find a more general `CTerm` which can instantiate to both.

        Args:
            other: other `CTerm` to consider for finding a more general `CTerm` with this one.
            keep_values: do not discard information about abstracted variables in returned result.
            kdef (optional): `KDefinition` to make analysis more precise.

        Returns:
            A tuple ``(cterm, csubst1, csubst2)`` where

            - ``cterm``: More general `CTerm` than either `self` or `other`.
            - ``csubst1``: Constrained substitution to apply to `cterm` to obtain `self`.
            - ``csubst2``: Constrained substitution to apply to `cterm` to obtain `other`.
        """
        new_config, self_subst, other_subst = anti_unify(self.config, other.config, kdef=kdef)
        common_constraints = [constraint for constraint in self.constraints if constraint in other.constraints]
        self_unique_constraints = [
            ml_pred_to_bool(constraint) for constraint in self.constraints if constraint not in other.constraints
        ]
        other_unique_constraints = [
            ml_pred_to_bool(constraint) for constraint in other.constraints if constraint not in self.constraints
        ]

        new_cterm = CTerm(config=new_config, constraints=())
        if keep_values:
            disjunct_lhs = andBool([self_subst.pred] + self_unique_constraints)
            disjunct_rhs = andBool([other_subst.pred] + other_unique_constraints)
            if KToken('true', 'Bool') not in [disjunct_lhs, disjunct_rhs]:
                new_cterm = new_cterm.add_constraint(mlEqualsTrue(orBool([disjunct_lhs, disjunct_rhs])))

        new_constraints = []
        fvs = new_cterm.free_vars
        len_fvs = 0
        while len_fvs < len(fvs):
            len_fvs = len(fvs)
            for constraint in common_constraints:
                if constraint not in new_constraints:
                    constraint_fvs = free_vars(constraint)
                    if any(fv in fvs for fv in constraint_fvs):
                        new_constraints.append(constraint)
                        fvs = fvs | constraint_fvs

        for constraint in new_constraints:
            new_cterm = new_cterm.add_constraint(constraint)
        self_csubst = new_cterm.match_with_constraint(self)
        other_csubst = new_cterm.match_with_constraint(other)
        if self_csubst is None or other_csubst is None:
            raise ValueError(
                f'Anti-unification failed to produce a more general state: {(new_cterm, (self, self_csubst), (other, other_csubst))}'
            )
        return (new_cterm, self_csubst, other_csubst)

    def remove_useless_constraints(self, keep_vars: Iterable[str] = ()) -> CTerm:
        """Return a new `CTerm` with constraints over unbound variables removed.

        Args:
            keep_vars: List of variables to keep constraints for even if unbound in the `CTerm`.

        Returns:
            A `CTerm` with the constraints over unbound variables removed.
        """
        initial_vars = free_vars(self.config) | set(keep_vars)
        new_constraints = remove_useless_constraints(self.constraints, initial_vars)
        return CTerm(self.config, new_constraints)


def anti_unify(state1: KInner, state2: KInner, kdef: KDefinition | None = None) -> tuple[KInner, Subst, Subst]:
    """Return a generalized state over the two input states.

    Args:
        state1: State to generalize over, represented as bare `KInner`.
        state2: State to generalize over, represented as bare `KInner`.
        kdef (optional): `KDefinition` to make the analysis more precise.

    Note:
        Both `state1` and `state2` are expected to be bare configurations with no constraints attached.

    Returns:
        A tuple ``(state, subst1, subst2)`` such that

        - ``state``: A symbolic state represented as `KInner` which is more general than `state1` or `state2`.
        - ``subst1``: A `Subst` which, when applied to `state`, recovers `state1`.
        - ``subst2``: A `Subst` which, when applied to `state`, recovers `state2`.
    """

    def _rewrites_to_abstractions(_kast: KInner) -> KInner:
        if type(_kast) is KRewrite:
            sort = kdef.sort(_kast) if kdef else None
            return abstract_term_safely(_kast, sort=sort)
        return _kast

    minimized_rewrite = push_down_rewrites(KRewrite(state1, state2))
    abstracted_state = bottom_up(_rewrites_to_abstractions, minimized_rewrite)
    subst1 = abstracted_state.match(state1)
    subst2 = abstracted_state.match(state2)
    if subst1 is None or subst2 is None:
        raise ValueError('Anti-unification failed to produce a more general state!')
    return (abstracted_state, subst1, subst2)


@dataclass(frozen=True, order=True)
class CSubst:
    """Store information about instantiation of a symbolic state (`CTerm`) to a more specific one.

    Contains the data:
    - `subst`: assignment to apply to free variables in the state to achieve more specific one
    - `constraints`: additional constraints over the free variables of the original state and the `subst` to add to the new state
    """

    subst: Subst
    constraints: tuple[KInner, ...]

    def __init__(self, subst: Subst | None = None, constraints: Iterable[KInner] = ()) -> None:
        """Construct a new `CSubst` given a `Subst` and set of constraints as `KInner`, performing basic sanity checks."""
        object.__setattr__(self, 'subst', subst if subst is not None else Subst({}))
        object.__setattr__(self, 'constraints', normalize_constraints(constraints))

    def __iter__(self) -> Iterator[Subst | KInner]:
        """Return an iterator with the head being the `subst` and the tail being the `constraints`."""
        return chain([self.subst], self.constraints)

    def to_dict(self) -> dict[str, Any]:
        """Serialize `CSubst` to dictionary representation."""
        return {
            'subst': self.subst.to_dict(),
            'constraints': [c.to_dict() for c in self.constraints],
        }

    @staticmethod
    def from_dict(dct: dict[str, Any]) -> CSubst:
        """Deserialize `CSubst` from a dictionary representation."""
        subst = Subst.from_dict(dct['subst'])
        constraints = (KInner.from_dict(c) for c in dct['constraints'])
        return CSubst(subst=subst, constraints=constraints)

    @property
    def constraint(self) -> KInner:
        """Return the set of constraints as a single flattened constraint using `mlAnd`."""
        return mlAnd(self.constraints)

    def add_constraint(self, constraint: KInner) -> CSubst:
        """Return this `CSubst` with an additional constraint added."""
        return CSubst(self.subst, list(self.constraints) + [constraint])

    def apply(self, cterm: CTerm) -> CTerm:
        """Apply this `CSubst` to the given `CTerm` (instantiating the free variables, and adding the constraints)."""
        _kast = self.subst(cterm.kast)
        return CTerm(_kast, [self.constraint])


def cterm_build_claim(
    claim_id: str, init_cterm: CTerm, final_cterm: CTerm, keep_vars: Iterable[str] = ()
) -> tuple[KClaim, Subst]:
    """Return a `KClaim` between the supplied initial and final states.

    Args:
        claim_id: Label to give the claim.
        init_cterm: State to put on LHS of the rule (constraints interpreted as `requires` clause).
        final_cterm: State to put on RHS of the rule (constraints interpreted as `ensures` clause).
        keep_vars: Variables to leave in the side-conditions even if not bound in the configuration.

    Returns:
        A tuple ``(claim, var_map)`` where

      - ``claim``: A `KClaim` with variable naming conventions applied
        so that it should be parseable by the K Frontend.
      - ``var_map``: The variable renamings applied to make the claim parseable by the K Frontend
        (which can be undone to recover original variables).
    """
    init_config, *init_constraints = init_cterm
    final_config, *final_constraints = final_cterm
    return build_claim(claim_id, init_config, final_config, init_constraints, final_constraints, keep_vars=keep_vars)


def cterm_build_rule(
    rule_id: str,
    init_cterm: CTerm,
    final_cterm: CTerm,
    priority: int | None = None,
    keep_vars: Iterable[str] = (),
    defunc_with: KDefinition | None = None,
) -> tuple[KRule, Subst]:
    """Return a `KRule` between the supplied initial and final states.

    Args:
        rule_id: Label to give the rule.
        init_cterm: State to put on LHS of the rule (constraints interpreted as `requires` clause).
        final_cterm: State to put on RHS of the rule (constraints interpreted as `ensures` clause).
        keep_vars: Variables to leave in the side-conditions even if not bound in the configuration.
        priority: Priority index to use for generated rules.
        defunc_with (optional): KDefinition to be able to defunctionalize LHS appropriately.

    Returns:
        A tuple ``(rule, var_map)`` where

      - ``rule``: A `KRule` with variable naming conventions applied
        so that it should be parseable by the K Frontend.
      - ``var_map``: The variable renamings applied to make the rule parseable by the K Frontend
        (which can be undone to recover original variables).
    """
    init_config, *init_constraints = init_cterm
    final_config, *final_constraints = final_cterm
    return build_rule(
        rule_id,
        init_config,
        final_config,
        init_constraints,
        final_constraints,
        priority,
        keep_vars,
        defunc_with=defunc_with,
    )
