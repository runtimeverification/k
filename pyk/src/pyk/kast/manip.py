from __future__ import annotations

import logging
from collections import Counter
from typing import TYPE_CHECKING

from ..prelude.k import DOTS, GENERATED_TOP_CELL
from ..prelude.kbool import FALSE, TRUE, andBool, impliesBool, notBool, orBool
from ..prelude.ml import mlAnd, mlEqualsTrue, mlOr
from ..utils import find_common_items, hash_str
from .inner import (
    KApply,
    KLabel,
    KRewrite,
    KSequence,
    KToken,
    KVariable,
    Subst,
    bottom_up,
    collect,
    top_down,
    var_occurrences,
)
from .kast import EMPTY_ATT, KAtt, WithKAtt
from .outer import KDefinition, KFlatModule, KRuleLike

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable
    from typing import Any, Final, TypeVar

    from .inner import KInner, KSort
    from .kast import AttKey

    KI = TypeVar('KI', bound=KInner)
    W = TypeVar('W', bound=WithKAtt)
    RL = TypeVar('RL', bound=KRuleLike)

_LOGGER: Final = logging.getLogger(__name__)


def flatten_label(label: str, kast: KInner) -> list[KInner]:
    """Given a cons list, return a flat Python list of the elements.

    -   Input: Cons operation to flatten.
    -   Output: Items of cons list.
    """
    if type(kast) is KApply and kast.label.name == label:
        items = (flatten_label(label, arg) for arg in kast.args)
        return [c for cs in items for c in cs]
    return [kast]


def is_term_like(kast: KInner) -> bool:
    non_term_found = False

    def _is_term_like(_kast: KInner) -> None:
        nonlocal non_term_found
        match _kast:
            case KVariable(name, _):
                if name.startswith('@'):
                    non_term_found = True
            case KApply(KLabel(name, _), _):
                if name in {
                    '#Equals',
                    '#And',
                    '#Or',
                    '#Top',
                    '#Bottom',
                    '#Implies',
                    '#Not',
                    '#Ceil',
                    '#Forall',
                    '#Exists',
                }:
                    non_term_found = True

    collect(_is_term_like, kast)
    return not non_term_found


def sort_assoc_label(label: str, kast: KInner) -> KInner:
    res: KInner | None = None
    if type(kast) is KApply and kast.label.name == label:
        terms = sorted(flatten_label(label, kast))
        for term in reversed(terms):
            if not res:
                res = term
            else:
                res = kast.label(term, res)
        assert res is not None
        return res
    return kast


def sort_ac_collections(kast: KInner) -> KInner:
    def _sort_ac_collections(_kast: KInner) -> KInner:
        if type(_kast) is KApply and (_kast.label.name in {'_Set_', '_Map_'} or _kast.label.name.endswith('CellMap_')):
            return sort_assoc_label(_kast.label.name, _kast)
        return _kast

    return top_down(_sort_ac_collections, kast)


def if_ktype(ktype: type[KI], then: Callable[[KI], KInner]) -> Callable[[KInner], KInner]:
    def fun(term: KInner) -> KInner:
        if isinstance(term, ktype):
            return then(term)
        return term

    return fun


def bool_to_ml_pred(kast: KInner) -> KInner:
    return mlAnd([mlEqualsTrue(cond) for cond in flatten_label('_andBool_', kast)])


def ml_pred_to_bool(kast: KInner, unsafe: bool = False) -> KInner:
    def _ml_constraint_to_bool(_kast: KInner) -> KInner:
        if type(_kast) is KApply:
            if _kast.label.name == '#Top':
                return TRUE
            if _kast.label.name == '#Bottom':
                return FALSE
            if _kast.label.name == '#Not' and len(_kast.args) == 1:
                return notBool(_ml_constraint_to_bool(_kast.args[0]))
            if _kast.label.name == '#And':
                return andBool(map(_ml_constraint_to_bool, _kast.args))
            if _kast.label.name == '#Or':
                return orBool(map(_ml_constraint_to_bool, _kast.args))
            if _kast.label.name == '#Implies' and len(_kast.args) == 2:
                return impliesBool(_ml_constraint_to_bool(_kast.args[0]), _ml_constraint_to_bool(_kast.args[1]))
            if _kast.label.name == '#Equals':
                first, second = _kast.args
                if first == TRUE:
                    return second
                if first == FALSE:
                    return notBool(second)
                if second == TRUE:
                    return first
                if second == FALSE:
                    return notBool(first)
                if type(first) in [KVariable, KToken]:
                    return KApply('_==K_', _kast.args)
                if type(first) is KSequence and type(second) is KSequence:
                    if first.arity == 1 and second.arity == 1:
                        return KApply('_==K_', (first.items[0], second.items[0]))
                if is_term_like(first) and is_term_like(second):
                    return KApply('_==K_', first, second)
            if unsafe:
                if _kast.label.name == '#Equals':
                    return KApply('_==K_', _kast.args)
                if _kast.label.name == '#Ceil':
                    ceil_var = abstract_term_safely(_kast, base_name='Ceil')
                    _LOGGER.warning(f'Converting #Ceil condition to variable {ceil_var.name}: {_kast}')
                    return ceil_var
                if _kast.label.name == '#Exists':
                    exists_var = abstract_term_safely(_kast, base_name='Exists')
                    _LOGGER.warning(f'Converting #Exists condition to variable {exists_var.name}: {_kast}')
                    return exists_var
        raise ValueError(f'Could not convert ML predicate to sort Bool: {_kast}')

    return _ml_constraint_to_bool(kast)


def simplify_bool(k: KInner) -> KInner:
    if k is None:
        return None

    # fmt: off
    simplify_rules = [ (KApply('_==K_', [KVariable('#LHS'), TRUE]), KVariable('#LHS'))
                     , (KApply('_==K_', [TRUE, KVariable('#RHS')]), KVariable('#RHS'))
                     , (KApply('_==K_', [KVariable('#LHS'), FALSE]), notBool(KVariable('#LHS')))
                     , (KApply('_==K_', [FALSE, KVariable('#RHS')]), notBool(KVariable('#RHS')))
                     , (notBool(FALSE), TRUE)
                     , (notBool(TRUE), FALSE)
                     , (notBool(KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')])), KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')]))
                     , (notBool(KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')])), KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')]))
                     , (notBool(KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')])), KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')]))
                     , (notBool(KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')])), KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')]))
                     , (andBool([TRUE, KVariable('#REST')]), KVariable('#REST'))
                     , (andBool([KVariable('#REST'), TRUE]), KVariable('#REST'))
                     , (andBool([FALSE, KVariable('#REST')]), FALSE)
                     , (andBool([KVariable('#REST'), FALSE]), FALSE)
                     , (orBool([FALSE, KVariable('#REST')]), KVariable('#REST'))
                     , (orBool([KVariable('#REST'), FALSE]), KVariable('#REST'))
                     , (orBool([TRUE, KVariable('#REST')]), TRUE)
                     , (orBool([KVariable('#REST'), TRUE]), TRUE)
                     ]
    # fmt: on

    new_k = k
    for rule in simplify_rules:
        rewrite = KRewrite(*rule)
        new_k = rewrite(new_k)
    return new_k


def extract_lhs(term: KInner) -> KInner:
    return top_down(if_ktype(KRewrite, lambda rw: rw.lhs), term)


def extract_rhs(term: KInner) -> KInner:
    return top_down(if_ktype(KRewrite, lambda rw: rw.rhs), term)


def extract_subst(term: KInner) -> tuple[Subst, KInner]:
    def _subst_for_terms(term1: KInner, term2: KInner) -> Subst | None:
        if type(term1) is KVariable and type(term2) not in {KToken, KVariable}:
            return Subst({term1.name: term2})
        if type(term2) is KVariable and type(term1) not in {KToken, KVariable}:
            return Subst({term2.name: term1})
        return None

    def _extract_subst(conjunct: KInner) -> Subst | None:
        if type(conjunct) is KApply:
            if conjunct.label.name == '#Equals':
                subst = _subst_for_terms(conjunct.args[0], conjunct.args[1])

                if subst is not None:
                    return subst

                if (
                    conjunct.args[0] == TRUE
                    and type(conjunct.args[1]) is KApply
                    and conjunct.args[1].label.name in {'_==K_', '_==Int_'}
                ):
                    subst = _subst_for_terms(conjunct.args[1].args[0], conjunct.args[1].args[1])

                    if subst is not None:
                        return subst

        return None

    conjuncts = flatten_label('#And', term)
    subst = Subst()
    rem_conjuncts: list[KInner] = []

    for conjunct in conjuncts:
        new_subst = _extract_subst(conjunct)
        if new_subst is None:
            rem_conjuncts.append(conjunct)
        else:
            new_subst = subst.union(new_subst)
            if new_subst is None:
                raise ValueError('Conflicting substitutions')  # TODO handle this case
            subst = new_subst

    return subst, mlAnd(rem_conjuncts)


def count_vars(term: KInner) -> Counter[str]:
    counter: Counter[str] = Counter()
    occurrences = var_occurrences(term)
    for vname in occurrences:
        counter[vname] = len(occurrences[vname])
    return counter


def free_vars(kast: KInner) -> list[str]:
    return list(count_vars(kast).keys())


def propagate_up_constraints(k: KInner) -> KInner:
    def _propagate_up_constraints(_k: KInner) -> KInner:
        if not (type(_k) is KApply and _k.label.name == '#Or'):
            return _k
        top_sort = _k.label.params[0]
        conjuncts1 = flatten_label('#And', _k.args[0])
        conjuncts2 = flatten_label('#And', _k.args[1])
        (common1, l1, r1) = find_common_items(conjuncts1, conjuncts2)
        (common2, r2, l2) = find_common_items(r1, l1)
        common = common1 + common2
        if len(common) == 0:
            return _k
        conjunct1 = mlAnd(l2, sort=top_sort)
        conjunct2 = mlAnd(r2, sort=top_sort)
        disjunct = mlOr([conjunct1, conjunct2], sort=top_sort)
        return mlAnd([disjunct] + common, sort=top_sort)

    return bottom_up(_propagate_up_constraints, k)


def split_config_and_constraints(kast: KInner) -> tuple[KInner, KInner]:
    conjuncts = flatten_label('#And', kast)
    term = None
    constraints = []
    for c in conjuncts:
        if type(c) is KApply and c.is_cell:
            if term:
                raise ValueError(f'Found two configurations in pattern:\n\n{term}\n\nand\n\n{c}')
            term = c
        else:
            constraints.append(c)
    if not term:
        raise ValueError(f'Could not find configuration for: {kast}')
    return (term, mlAnd(constraints, GENERATED_TOP_CELL))


def cell_label_to_var_name(label: str) -> str:
    """Return a variable name based on a cell label."""
    return label.replace('-', '_').replace('<', '').replace('>', '').upper() + '_CELL'


def split_config_from(configuration: KInner) -> tuple[KInner, dict[str, KInner]]:
    """Split the substitution from a given configuration.

    Given an input configuration `config`, will return a tuple `(symbolic_config, subst)`, where:

        1.  `config == substitute(symbolic_config, subst)`
        2.  `symbolic_config` is the same configuration structure, but where the contents of leaf cells is replaced with a fresh KVariable.
        3.  `subst` is the substitution for the generated KVariables back to the original configuration contents.
    """
    initial_substitution = {}

    def _replace_with_var(k: KInner) -> KInner:
        if type(k) is KApply and k.is_cell:
            if k.arity == 1 and not (type(k.args[0]) is KApply and k.args[0].is_cell):
                config_var = cell_label_to_var_name(k.label.name)
                initial_substitution[config_var] = k.args[0]
                return KApply(k.label, [KVariable(config_var)])
        return k

    symbolic_config = top_down(_replace_with_var, configuration)
    return (symbolic_config, initial_substitution)


def collapse_dots(kast: KInner) -> KInner:
    """Given a configuration with structural frames `...`, minimize the structural frames needed.

    -   Input: a configuration, potentially with structural frames.
    -   Output: the same configuration, with the amount of structural framing minimized.
    """

    def _collapse_dots(_kast: KInner) -> KInner:
        if type(_kast) is KApply:
            if _kast.is_cell and _kast.arity == 1 and _kast.args[0] == DOTS:
                return DOTS
            new_args = [arg for arg in _kast.args if arg != DOTS]
            if _kast.is_cell and len(new_args) == 0:
                return DOTS
            if len(new_args) < len(_kast.args):
                new_args.append(DOTS)
            return _kast.let(args=new_args)
        elif type(_kast) is KRewrite:
            if _kast.lhs == DOTS:
                return DOTS
        return _kast

    return bottom_up(_collapse_dots, kast)


def push_down_rewrites(kast: KInner) -> KInner:
    def _push_down_rewrites(_kast: KInner) -> KInner:
        if type(_kast) is KRewrite:
            lhs = _kast.lhs
            rhs = _kast.rhs
            if lhs == rhs:
                return lhs
            if type(lhs) is KVariable and type(rhs) is KVariable and lhs.name == rhs.name:
                return lhs
            if type(lhs) is KApply and type(rhs) is KApply and lhs.label == rhs.label and lhs.arity == rhs.arity:
                new_args = [
                    KRewrite(left_arg, right_arg) for left_arg, right_arg in zip(lhs.args, rhs.args, strict=True)
                ]
                return lhs.let(args=new_args)
            if type(lhs) is KSequence and type(rhs) is KSequence and lhs.arity > 0 and rhs.arity > 0:
                if lhs.arity == 1 and rhs.arity == 1:
                    return KRewrite(lhs.items[0], rhs.items[0])
                if lhs.items[0] == rhs.items[0]:
                    lower_rewrite = _push_down_rewrites(KRewrite(KSequence(lhs.items[1:]), KSequence(rhs.items[1:])))
                    return KSequence([lhs.items[0], lower_rewrite])
                if lhs.items[-1] == rhs.items[-1]:
                    lower_rewrite = _push_down_rewrites(
                        KRewrite(KSequence(lhs.items[0:-1]), KSequence(rhs.items[0:-1]))
                    )
                    return KSequence([lower_rewrite, lhs.items[-1]])
            if (
                type(lhs) is KSequence
                and lhs.arity > 0
                and type(lhs.items[-1]) is KVariable
                and type(rhs) is KVariable
                and lhs.items[-1] == rhs
            ):
                return KSequence([KRewrite(KSequence(lhs.items[0:-1]), KSequence([])), rhs])
        return _kast

    return top_down(_push_down_rewrites, kast)


def inline_cell_maps(kast: KInner) -> KInner:
    """Ensure that cell map collections are printed nicely, not as Maps."

    -   Input: kast term.
    -   Output: kast term with cell maps inlined.
    """

    def _inline_cell_maps(_kast: KInner) -> KInner:
        if type(_kast) is KApply and _kast.label.name.endswith('CellMapItem'):
            map_key = _kast.args[0]
            if type(map_key) is KApply and map_key.is_cell:
                return _kast.args[1]
        return _kast

    return bottom_up(_inline_cell_maps, kast)


def remove_semantic_casts(kast: KInner) -> KInner:
    """Remove injected `#SemanticCast*` nodes in AST.

    -   Input: kast (possibly) containing automatically injected `#SemanticCast*` KApply nodes.
    -   Output: kast without the `#SemanticCast*` nodes.
    """

    def _remove_semtnaic_casts(_kast: KInner) -> KInner:
        if type(_kast) is KApply and _kast.arity == 1 and _kast.label.name.startswith('#SemanticCast'):
            return _kast.args[0]
        return _kast

    return bottom_up(_remove_semtnaic_casts, kast)


def useless_vars_to_dots(kast: KInner, keep_vars: Iterable[str] = ()) -> KInner:
    """Structurally abstract away useless variables.

    -   Input: kast term, and a requires clause and ensures clause.
    -   Output: kast term with the useless vars structurally abstracted.
    """
    num_occs = count_vars(kast) + Counter(keep_vars)

    def _collapse_useless_vars(_kast: KInner) -> KInner:
        if type(_kast) is KApply and _kast.is_cell:
            new_args: list[KInner] = []
            for arg in _kast.args:
                if type(arg) is KVariable and num_occs[arg.name] == 1:
                    new_args.append(DOTS)
                else:
                    new_args.append(arg)
            return _kast.let(args=new_args)
        return _kast

    return bottom_up(_collapse_useless_vars, kast)


def labels_to_dots(kast: KInner, labels: Collection[str]) -> KInner:
    """Abstract specific labels for printing.

    -   Input: kast term, and list of labels to abstract.
    -   Output: kast term with those labels abstracted.
    """

    def _labels_to_dots(k: KInner) -> KInner:
        if type(k) is KApply and k.is_cell and k.label.name in labels:
            return DOTS
        return k

    return bottom_up(_labels_to_dots, kast)


def extract_cells(kast: KInner, keep_cells: Collection[str]) -> KInner:
    def _extract_cells(k: KInner) -> KInner:
        if (
            type(k) is KApply
            and k.is_cell
            and not k.label.name in keep_cells
            and all(type(arg) != KApply or not arg.is_cell or arg == DOTS for arg in k.args)
        ):
            return DOTS
        return k

    return bottom_up(_extract_cells, kast)


def on_attributes(kast: W, f: Callable[[KAtt], KAtt]) -> W:
    kast = kast.map_att(f)

    # TODO mypy bug: https://github.com/python/mypy/issues/10817

    if type(kast) is KFlatModule:
        sentences = (sentence.map_att(f) for sentence in kast.sentences)
        return kast.let(sentences=sentences)  # type: ignore

    if type(kast) is KDefinition:
        modules = (module.map_att(f) for module in kast.modules)
        return kast.let(modules=modules)  # type: ignore

    return kast


def minimize_term(
    term: KInner, keep_vars: Iterable[str] = (), abstract_labels: Collection[str] = (), keep_cells: Collection[str] = ()
) -> KInner:
    """Minimize a K term for pretty-printing.

    -   Input: kast term, and optionally requires and ensures clauses with constraints.
    -   Output: kast term minimized.
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless conditions.
    """

    term = inline_cell_maps(term)
    term = remove_semantic_casts(term)
    term = useless_vars_to_dots(term, keep_vars=keep_vars)

    if keep_cells:
        term = extract_cells(term, keep_cells)
    else:
        term = labels_to_dots(term, abstract_labels)

    term = collapse_dots(term)

    return term


def minimize_rule(rule: RL, keep_vars: Iterable[str] = ()) -> RL:
    """Minimize a K rule or claim for pretty-printing.

    -   Input: kast representing a K rule or claim.
    -   Output: kast with the rule or claim minimized:
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless side-conditions.
    """
    body = rule.body
    requires = rule.requires
    ensures = rule.ensures

    requires = andBool(flatten_label('_andBool_', requires))
    requires = simplify_bool(requires)

    ensures = andBool(flatten_label('_andBool_', ensures))
    ensures = simplify_bool(ensures)

    constrained_vars = list(keep_vars)
    constrained_vars = constrained_vars + free_vars(requires)
    constrained_vars = constrained_vars + free_vars(ensures)
    body = minimize_term(body, keep_vars=constrained_vars)

    return rule.let(body=body, requires=requires, ensures=ensures)


def remove_source_map(definition: KDefinition) -> KDefinition:
    return on_attributes(definition, lambda att: att.drop_source())


def remove_attrs(term: KInner) -> KInner:
    def remove_attr(term: KInner) -> KInner:
        if isinstance(term, WithKAtt):
            return term.let_att(EMPTY_ATT)
        return term

    return top_down(remove_attr, term)


def remove_source_attributes(term: KInner) -> KInner:
    def _is_not_source_att(att: tuple[AttKey, Any]) -> bool:
        return att[0] not in (KAtt.SOURCE, KAtt.LOCATION)

    def _remove_source_attr(term: KInner) -> KInner:
        if not isinstance(term, WithKAtt):
            return term
        return term.let_att(KAtt(dict(filter(_is_not_source_att, term.att.items()))))

    return top_down(_remove_source_attr, term)


def remove_generated_cells(term: KInner) -> KInner:
    """Remove <generatedTop> and <generatedCounter> from a configuration.

    -   Input: Constrained term.
    -   Output: Constrained term with those cells removed.
    """
    rewrite = KRewrite(KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG'))
    return rewrite(term)


def is_anon_var(kast: KInner) -> bool:
    return type(kast) is KVariable and kast.name.startswith('_')


def omit_large_tokens(kast: KInner, max_len: int = 78) -> KInner:
    def _large_tokens_to_dots(_k: KInner) -> KInner:
        if type(_k) is KToken and len(_k.token) > max_len:
            return KToken('...', _k.sort)
        return _k

    return bottom_up(_large_tokens_to_dots, kast)


def get_cell(constrained_term: KInner, cell_variable: str) -> KInner:
    state, _ = split_config_and_constraints(constrained_term)
    _, subst = split_config_from(state)
    return subst[cell_variable]


def set_cell(constrained_term: KInner, cell_variable: str, cell_value: KInner) -> KInner:
    state, constraint = split_config_and_constraints(constrained_term)
    config, subst = split_config_from(state)
    subst[cell_variable] = cell_value
    return mlAnd([Subst(subst)(config), constraint])


def remove_constraint_clauses_for(var_names: Collection[str], constraint: KInner) -> KInner:
    constraints = flatten_label('#And', constraint)
    new_constraints = []
    for c in constraints:
        if not any(v in var_names for v in free_vars(c)):
            new_constraints.append(c)
    return mlAnd(new_constraints)


def remove_constraints_for(var_names: Collection[str], constrained_term: KInner) -> KInner:
    state, constraint = split_config_and_constraints(constrained_term)
    constraint = remove_constraint_clauses_for(var_names, constraint)
    return mlAnd([state, constraint])


def abstract_term_safely(
    kast: KInner, base_name: str = 'V', sort: KSort | None = None, existing_var_names: set[str] | None = None
) -> KVariable:
    def _abstract(k: KInner) -> KVariable:
        vname = hash_str(k)[0:8]
        return KVariable(base_name + '_' + vname, sort=sort)

    new_var = _abstract(kast)
    if existing_var_names is not None:
        while new_var.name in existing_var_names:
            new_var = _abstract(new_var)
    return new_var


def apply_existential_substitutions(constrained_term: KInner) -> KInner:
    state, constraint = split_config_and_constraints(constrained_term)
    constraints = flatten_label('#And', constraint)
    pattern = mlEqualsTrue(KApply('_==K_', [KVariable('#VAR'), KVariable('#VAL')]))
    subst = {}
    new_constraints = []
    for c in constraints:
        match = pattern.match(c)
        if match is not None and type(match['#VAR']) is KVariable and match['#VAR'].name.startswith('?'):
            subst[match['#VAR'].name] = match['#VAL']
        else:
            new_constraints.append(c)
    return Subst(subst)(mlAnd([state] + new_constraints))


def indexed_rewrite(kast: KInner, rewrites: Iterable[KRewrite]) -> KInner:
    token_rewrites: list[KRewrite] = []
    apply_rewrites: dict[str, list[KRewrite]] = {}
    other_rewrites: list[KRewrite] = []
    for r in rewrites:
        if type(r.lhs) is KToken:
            token_rewrites.append(r)
        elif type(r.lhs) is KApply:
            if r.lhs.label.name in token_rewrites:
                apply_rewrites[r.lhs.label.name].append(r)
            else:
                apply_rewrites[r.lhs.label.name] = [r]
        else:
            other_rewrites.append(r)

    def _apply_rewrites(_kast: KInner) -> KInner:
        if type(_kast) is KToken:
            for tr in token_rewrites:
                _kast = tr.apply_top(_kast)
        elif type(_kast) is KApply:
            if _kast.label.name in apply_rewrites:
                for ar in apply_rewrites[_kast.label.name]:
                    _kast = ar.apply_top(_kast)
        else:
            for _or in other_rewrites:
                _kast = _or.apply_top(_kast)
        return _kast

    orig_kast: KInner = kast
    new_kast: KInner | None = None
    while orig_kast != new_kast:
        if new_kast is None:
            new_kast = orig_kast
        else:
            orig_kast = new_kast
        new_kast = bottom_up(_apply_rewrites, new_kast)
    return new_kast


def undo_aliases(definition: KDefinition, kast: KInner) -> KInner:
    aliases = []
    for rule in definition.alias_rules:
        rewrite = rule.body
        if type(rewrite) is not KRewrite:
            raise ValueError(f'Expected KRewrite as alias body, found: {rewrite}')
        if rule.requires is not None and rule.requires != TRUE:
            raise ValueError(f'Expended empty requires clause on alias, found: {rule.requires}')
        if rule.ensures is not None and rule.ensures != TRUE:
            raise ValueError(f'Expended empty ensures clause on alias, found: {rule.ensures}')
        aliases.append(KRewrite(rewrite.rhs, rewrite.lhs))
    return indexed_rewrite(kast, aliases)


def rename_generated_vars(term: KInner) -> KInner:
    vars: set[str] = set(free_vars(term))
    cell_stack: list[str] = []

    def _rename_vars(k: KInner) -> KInner:
        if type(k) is KApply and k.is_cell:
            cell_stack.append(cell_label_to_var_name(k.label.name))
            res = k.map_inner(_rename_vars)
            cell_stack.pop()
            return res

        if type(k) is KVariable and k.name.startswith(('_Gen', '?_Gen', '_DotVar', '?_DotVar')):
            if not cell_stack:
                return k
            cell_name = cell_stack[-1]
            new_var = abstract_term_safely(k, base_name=cell_name, sort=k.sort, existing_var_names=vars)
            vars.add(new_var.name)
            return new_var

        return k.map_inner(_rename_vars)

    return _rename_vars(term)
