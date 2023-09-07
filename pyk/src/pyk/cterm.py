from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property
from itertools import chain
from typing import TYPE_CHECKING

from .kast.inner import KApply, KInner, KRewrite, KToken, KVariable, Subst, bottom_up
from .kast.kast import KAtt
from .kast.manip import (
    abstract_term_safely,
    apply_existential_substitutions,
    count_vars,
    flatten_label,
    free_vars,
    minimize_rule,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    simplify_bool,
    split_config_and_constraints,
    split_config_from,
)
from .kast.outer import KClaim, KRule
from .prelude.k import GENERATED_TOP_CELL
from .prelude.kbool import andBool, orBool
from .prelude.ml import is_bottom, is_top, mlAnd, mlBottom, mlEqualsTrue, mlImplies, mlTop
from .utils import single, unique

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Any

    from .kast.outer import KDefinition


@dataclass(frozen=True, order=True)
class CTerm:
    config: KInner  # TODO Optional?
    constraints: tuple[KInner, ...]

    def __init__(self, config: KInner, constraints: Iterable[KInner] = ()) -> None:
        if CTerm._is_top(config):
            config = mlTop()
            constraints = ()
        elif CTerm._is_bottom(config):
            config = mlBottom()
            constraints = ()
        else:
            self._check_config(config)
            constraints = self._normalize_constraints(constraints)
        object.__setattr__(self, 'config', config)
        object.__setattr__(self, 'constraints', constraints)

    @staticmethod
    def from_kast(kast: KInner) -> CTerm:
        if CTerm._is_top(kast):
            return CTerm.top()
        elif CTerm._is_bottom(kast):
            return CTerm.bottom()
        else:
            config, constraint = split_config_and_constraints(kast)
            constraints = flatten_label('#And', constraint)
            return CTerm(config, constraints)

    @staticmethod
    def from_dict(dct: dict[str, Any]) -> CTerm:
        config = KInner.from_dict(dct['config'])
        constraints = [KInner.from_dict(c) for c in dct['constraints']]
        return CTerm(config, constraints)

    @staticmethod
    def top() -> CTerm:
        return CTerm(mlTop(), ())

    @staticmethod
    def bottom() -> CTerm:
        return CTerm(mlBottom(), ())

    @staticmethod
    def _check_config(config: KInner) -> None:
        if not isinstance(config, KApply) or not config.is_cell:
            raise ValueError(f'Expected cell label, found: {config}')

    @staticmethod
    def _normalize_constraints(constraints: Iterable[KInner]) -> tuple[KInner, ...]:
        constraints = (constraint for _constraint in constraints for constraint in flatten_label('#And', _constraint))
        constraints = unique(constraints)
        constraints = (constraint for constraint in constraints if not CTerm._is_spurious_constraint(constraint))
        constraints = sorted(constraints, key=CTerm._constraint_sort_key)
        return tuple(constraints)

    @staticmethod
    def _is_spurious_constraint(term: KInner) -> bool:
        if type(term) is KApply and term.label.name == '#Equals' and term.args[0] == term.args[1]:
            return True
        if is_top(term):
            return True
        return False

    @staticmethod
    def _is_top(kast: KInner) -> bool:
        flat = flatten_label('#And', kast)
        if len(flat) == 1:
            return is_top(single(flat))
        return all(CTerm._is_top(term) for term in flat)

    @staticmethod
    def _is_bottom(kast: KInner) -> bool:
        flat = flatten_label('#And', kast)
        if len(flat) == 1:
            return is_bottom(single(flat))
        return all(CTerm._is_bottom(term) for term in flat)

    @staticmethod
    def _constraint_sort_key(term: KInner) -> tuple[int, str]:
        term_str = str(term)
        return (len(term_str), term_str)

    def __iter__(self) -> Iterator[KInner]:
        return chain([self.config], self.constraints)

    def to_dict(self) -> dict[str, Any]:
        return {
            'config': self.config.to_dict(),
            'constraints': [c.to_dict() for c in self.constraints],
        }

    @cached_property
    def kast(self) -> KInner:
        return mlAnd(self, GENERATED_TOP_CELL)

    @property
    def hash(self) -> str:
        return self.kast.hash

    @cached_property
    def cells(self) -> Subst:
        _, subst = split_config_from(self.config)
        return Subst(subst)

    def cell(self, cell: str) -> KInner:
        return self.cells[cell]

    def try_cell(self, cell: str) -> KInner | None:
        return self.cells.get(cell)

    def match(self, cterm: CTerm) -> Subst | None:
        csubst = self.match_with_constraint(cterm)

        if not csubst:
            return None

        if csubst.constraint != mlTop(GENERATED_TOP_CELL):
            return None

        return csubst.subst

    def match_with_constraint(self, cterm: CTerm) -> CSubst | None:
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
        return CTerm(self.config, [new_constraint] + list(self.constraints))

    def anti_unify(
        self, other: CTerm, keep_values: bool = False, kdef: KDefinition | None = None
    ) -> tuple[CTerm, CSubst, CSubst]:
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
        fvs = free_vars(new_cterm.kast)
        len_fvs = 0
        while len_fvs < len(fvs):
            len_fvs = len(fvs)
            for constraint in common_constraints:
                if constraint not in new_constraints:
                    constraint_fvs = free_vars(constraint)
                    if any(fv in fvs for fv in constraint_fvs):
                        new_constraints.append(constraint)
                        fvs.extend(constraint_fvs)

        for constraint in new_constraints:
            new_cterm = new_cterm.add_constraint(constraint)
        self_csubst = new_cterm.match_with_constraint(self)
        other_csubst = new_cterm.match_with_constraint(other)
        if self_csubst is None or other_csubst is None:
            raise ValueError(
                f'Anti-unification failed to produce a more general state: {(new_cterm, (self, self_csubst), (other, other_csubst))}'
            )
        return (new_cterm, self_csubst, other_csubst)


def anti_unify(state1: KInner, state2: KInner, kdef: KDefinition | None = None) -> tuple[KInner, Subst, Subst]:
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
    subst: Subst
    constraints: tuple[KInner, ...]

    def __init__(self, subst: Subst | None = None, constraints: Iterable[KInner] = ()) -> None:
        object.__setattr__(self, 'subst', subst if subst is not None else Subst({}))
        object.__setattr__(self, 'constraints', CTerm._normalize_constraints(constraints))

    def __iter__(self) -> Iterator[Subst | KInner]:
        return chain([self.subst], self.constraints)

    def to_dict(self) -> dict[str, Any]:
        return {
            'subst': self.subst.to_dict(),
            'constraints': [c.to_dict() for c in self.constraints],
        }

    @staticmethod
    def from_dict(dct: dict[str, Any]) -> CSubst:
        subst = Subst.from_dict(dct['subst'])
        constraints = (KInner.from_dict(c) for c in dct['constraints'])
        return CSubst(subst=subst, constraints=constraints)

    @property
    def constraint(self) -> KInner:
        return mlAnd(self.constraints)

    def add_constraint(self, constraint: KInner) -> CSubst:
        return CSubst(self.subst, list(self.constraints) + [constraint])

    def apply(self, cterm: CTerm) -> CTerm:
        _kast = self.subst(cterm.kast)
        return CTerm(_kast, [self.constraint])


def remove_useless_constraints(cterm: CTerm, keep_vars: Iterable[str] = ()) -> CTerm:
    used_vars = free_vars(cterm.config) + list(keep_vars)
    prev_len_unsed_vars = 0
    new_constraints = []
    while len(used_vars) > prev_len_unsed_vars:
        prev_len_unsed_vars = len(used_vars)
        for c in cterm.constraints:
            if c not in new_constraints:
                new_vars = free_vars(c)
                if any(v in used_vars for v in new_vars):
                    new_constraints.append(c)
                    used_vars.extend(new_vars)
        used_vars = list(set(used_vars))
    return CTerm(cterm.config, new_constraints)


def build_claim(
    claim_id: str, init_cterm: CTerm, final_cterm: CTerm, keep_vars: Iterable[str] = ()
) -> tuple[KClaim, Subst]:
    rule, var_map = build_rule(claim_id, init_cterm, final_cterm, keep_vars=keep_vars)
    claim = KClaim(rule.body, requires=rule.requires, ensures=rule.ensures, att=rule.att)
    return claim, var_map


def build_rule(
    rule_id: str,
    init_cterm: CTerm,
    final_cterm: CTerm,
    priority: int | None = None,
    keep_vars: Iterable[str] = (),
) -> tuple[KRule, Subst]:
    init_config, *init_constraints = init_cterm
    final_config, *final_constraints = final_cterm
    final_constraints = [c for c in final_constraints if c not in init_constraints]
    init_term = mlAnd([init_config] + init_constraints)
    final_term = mlAnd([final_config] + final_constraints)

    lhs_vars = free_vars(init_term)
    rhs_vars = free_vars(final_term)
    var_occurrences = count_vars(
        mlAnd(
            [push_down_rewrites(KRewrite(init_config, final_config))] + init_constraints + final_constraints,
            GENERATED_TOP_CELL,
        )
    )
    v_subst: dict[str, KVariable] = {}
    vremap_subst: dict[str, KVariable] = {}
    for v in var_occurrences:
        new_v = v
        if var_occurrences[v] == 1:
            new_v = '_' + new_v
        if v in rhs_vars and v not in lhs_vars:
            new_v = '?' + new_v
        if new_v != v:
            v_subst[v] = KVariable(new_v)
            vremap_subst[new_v] = KVariable(v)

    init_term = Subst(v_subst)(init_term)
    final_term = apply_existential_substitutions(Subst(v_subst)(final_term))
    (init_config, init_constraint) = split_config_and_constraints(init_term)
    (final_config, final_constraint) = split_config_and_constraints(final_term)

    rule_body = remove_generated_cells(push_down_rewrites(KRewrite(init_config, final_config)))
    rule_requires = simplify_bool(ml_pred_to_bool(init_constraint))
    rule_ensures = simplify_bool(ml_pred_to_bool(final_constraint))
    att_dict = {} if priority is None else {'priority': str(priority)}
    rule_att = KAtt(atts=att_dict)

    rule = KRule(rule_body, requires=rule_requires, ensures=rule_ensures, att=rule_att)
    rule = rule.update_atts({'label': rule_id})
    new_keep_vars = [v_subst[v].name if v in v_subst else v for v in keep_vars]
    return (minimize_rule(rule, keep_vars=new_keep_vars), Subst(vremap_subst))
