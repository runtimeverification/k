from dataclasses import dataclass
from functools import cached_property
from itertools import chain
from typing import Dict, Iterable, Optional, Tuple

from .kast import KApply, KAtt, KClaim, KInner, KRewrite, KRule, KVariable, Subst
from .kastManip import (
    apply_existential_substitutions,
    count_vars,
    flatten_label,
    free_vars,
    minimize_rule,
    ml_pred_to_bool,
    push_down_rewrites,
    simplify_bool,
    split_config_and_constraints,
    substitute,
)
from .prelude.k import GENERATED_TOP_CELL
from .prelude.ml import mlAnd, mlImplies, mlTop
from .utils import unique


@dataclass(frozen=True, order=True)
class CTerm:
    config: KInner  # TODO Optional?
    constraints: Tuple[KInner, ...]

    def __init__(self, term: KInner) -> None:
        config, constraint = split_config_and_constraints(term)
        constraints = CTerm._normalize_constraints(flatten_label('#And', constraint))
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
        return type(term) is KApply and term.label.name == '#Equals' and term.args[0] == term.args[1]

    @staticmethod
    def _constraint_sort_key(term: KInner) -> Tuple[int, str]:
        term_str = str(term)
        return (len(term_str), term_str)

    def __iter__(self):
        return chain([self.config], self.constraints)

    @cached_property
    def kast(self) -> KInner:
        return mlAnd(self, GENERATED_TOP_CELL)

    @property
    def hash(self) -> str:
        return self.kast.hash

    def match(self, cterm: 'CTerm') -> Optional[Subst]:
        match_res = self.match_with_constraint(cterm)

        if not match_res:
            return None

        subst, condition = match_res

        if condition != mlTop(GENERATED_TOP_CELL):
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
        antecedent = mlAnd(unique(antecedents), GENERATED_TOP_CELL)
        consequent = mlAnd(unique(term for term in consequents if term not in set(antecedents)), GENERATED_TOP_CELL)

        if mlTop(GENERATED_TOP_CELL) in {antecedent, consequent}:
            return consequent

        return mlImplies(antecedent, consequent, GENERATED_TOP_CELL)

    def add_constraint(self, new_constraint: KInner) -> 'CTerm':
        return CTerm(mlAnd([self.config, new_constraint] + list(self.constraints), GENERATED_TOP_CELL))


def remove_useless_constraints(cterm: CTerm, keep_vars=None) -> CTerm:
    used_vars = free_vars(cterm.config)
    used_vars = used_vars if keep_vars is None else (used_vars + keep_vars)
    prev_len_unsed_vars = 0
    new_constraints = []
    while len(used_vars) > prev_len_unsed_vars:
        prev_len_unsed_vars = len(used_vars)
        for c in cterm.constraints:
            if c not in new_constraints:
                new_vars = free_vars(c)
                if any([v in used_vars for v in new_vars]):
                    new_constraints.append(c)
                    used_vars.extend(new_vars)
        used_vars = list(set(used_vars))
    return CTerm(mlAnd([cterm.config] + new_constraints))


def build_claim(
    claim_id: str, init_cterm: CTerm, final_cterm: CTerm, keep_vars: Iterable[str] = ()
) -> Tuple[KClaim, Subst]:
    rule, var_map = build_rule(claim_id, init_cterm, final_cterm, keep_vars=keep_vars)
    claim = KClaim(rule.body, requires=rule.requires, ensures=rule.ensures, att=rule.att)
    return claim, var_map


def build_rule(
    rule_id: str,
    init_cterm: CTerm,
    final_cterm: CTerm,
    priority: Optional[int] = None,
    keep_vars: Iterable[str] = (),
) -> Tuple[KRule, Subst]:

    init_config, *init_constraints = init_cterm
    final_config, *final_constraints = final_cterm
    final_constraints = [c for c in final_constraints if c not in init_constraints]
    init_term = mlAnd([init_config] + init_constraints)
    final_term = mlAnd([final_config] + final_constraints)

    lhs_vars = free_vars(init_term)
    rhs_vars = free_vars(final_term)
    var_occurances = count_vars(
        mlAnd(
            [push_down_rewrites(KRewrite(init_config, final_config))] + init_constraints + final_constraints,
            GENERATED_TOP_CELL,
        )
    )
    v_subst: Dict[str, KVariable] = {}
    vremap_subst: Dict[str, KVariable] = {}
    for v in var_occurances:
        new_v = v
        if var_occurances[v] == 1:
            new_v = '_' + new_v
        if v in rhs_vars and v not in lhs_vars:
            new_v = '?' + new_v
        v_subst[v] = KVariable(new_v)
        vremap_subst[new_v] = KVariable(v)

    init_term = substitute(init_term, v_subst)
    final_term = apply_existential_substitutions(substitute(final_term, v_subst))
    (init_config, init_constraint) = split_config_and_constraints(init_term)
    (final_config, final_constraint) = split_config_and_constraints(final_term)

    rule_body = push_down_rewrites(KRewrite(init_config, final_config))
    rule_requires = simplify_bool(ml_pred_to_bool(init_constraint))
    rule_ensures = simplify_bool(ml_pred_to_bool(final_constraint))
    att_dict = {} if priority is None else {'priority': str(priority)}
    rule_att = KAtt(atts=att_dict)

    rule = KRule(rule_body, requires=rule_requires, ensures=rule_ensures, att=rule_att)
    rule = rule.update_atts({'label': rule_id})
    new_keep_vars = [v_subst[v].name for v in keep_vars]
    return (minimize_rule(rule, keep_vars=new_keep_vars), Subst(vremap_subst))
