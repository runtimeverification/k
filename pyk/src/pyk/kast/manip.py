from __future__ import annotations

import logging
from collections import Counter
from typing import TYPE_CHECKING

from ..prelude.k import DOTS, GENERATED_TOP_CELL
from ..prelude.kbool import FALSE, TRUE, andBool, impliesBool, notBool, orBool
from ..prelude.ml import is_top, mlAnd, mlBottom, mlEquals, mlEqualsTrue, mlImplies, mlOr, mlTop
from ..utils import find_common_items, hash_str, unique
from .att import EMPTY_ATT, Atts, KAtt, WithKAtt
from .inner import (
    KApply,
    KLabel,
    KRewrite,
    KSequence,
    KSort,
    KToken,
    KVariable,
    Subst,
    bottom_up,
    collect,
    flatten_label,
    top_down,
    var_occurrences,
)
from .outer import KClaim, KDefinition, KFlatModule, KRule, KRuleLike
from .rewrite import indexed_rewrite

if TYPE_CHECKING:
    from collections.abc import Callable, Collection, Iterable
    from typing import Final, TypeVar

    from .inner import KInner

    KI = TypeVar('KI', bound=KInner)
    W = TypeVar('W', bound=WithKAtt)
    RL = TypeVar('RL', bound=KRuleLike)

_LOGGER: Final = logging.getLogger(__name__)


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
        if type(_kast) is KApply and (
            _kast.label.name in {'_Set_', '_Map_', '_RangeMap_'} or _kast.label.name.endswith('CellMap_')
        ):
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
    def _bool_constraint_to_ml(_kast: KInner) -> KInner:
        if _kast == TRUE:
            return mlTop()
        if _kast == FALSE:
            return mlBottom()
        return mlEqualsTrue(_kast)

    return mlAnd([_bool_constraint_to_ml(cond) for cond in flatten_label('_andBool_', kast)])


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
                if isinstance(first, (KVariable, KToken)):
                    if first.sort == KSort('Int'):
                        return KApply('_==Int_', _kast.args)
                    else:
                        return KApply('_==K_', _kast.args)
                if isinstance(second, (KVariable, KToken)):
                    if second.sort == KSort('Int'):
                        return KApply('_==Int_', _kast.args)
                    else:
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


def normalize_ml_pred(pred: KInner) -> KInner:
    return bool_to_ml_pred(simplify_bool(ml_pred_to_bool(pred)))


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


def free_vars(kast: KInner) -> frozenset[str]:
    return frozenset(count_vars(kast).keys())


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

    Args:
        kast: A configuration, potentially with structural frames.

    Returns:
        The same configuration, with the amount of structural framing minimized.
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
    """Ensure that cell map collections are printed nicely, not as Maps.

    Args:
        kast: A KAST term.

    Returns:
        The KAST term with cell maps inlined.
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

    Args:
        kast: A term (possibly) containing automatically injected `#SemanticCast*` KApply nodes.

    Returns:
        The term without the `#SemanticCast*` nodes.
    """

    def _remove_semtnaic_casts(_kast: KInner) -> KInner:
        if type(_kast) is KApply and _kast.arity == 1 and _kast.label.name.startswith('#SemanticCast'):
            return _kast.args[0]
        return _kast

    return bottom_up(_remove_semtnaic_casts, kast)


def useless_vars_to_dots(kast: KInner, keep_vars: Iterable[str] = ()) -> KInner:
    """Structurally abstract away useless variables.

    Args:
        kast: A term.
        keep_vars: Iterable of variables to keep.

    Returns:
        The term with the useless varables structurally abstracted.
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

    Args:
        kast: A term.
        labels: List of labels to abstract.

    Returns
        The term with `labels` abstracted.
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

    - Variables only used once will be removed.
    - Unused cells will be abstracted.
    - Useless conditions will be attempted to be removed.

    Args:
        kast: A term.

    Returns:
        The term, minimized.
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


def minimize_rule_like(rule: RL, keep_vars: Iterable[str] = ()) -> RL:
    """Minimize a K rule or claim for pretty-printing.

    - Variables only used once will be removed.
    - Unused cells will be abstracted.
    - Useless side-conditions will be attempted to be removed.

    Args:
        rule: A K rule or claim.

    Returns:
        The rule or claim, minimized.
    """
    body = rule.body
    requires = rule.requires
    ensures = rule.ensures

    requires = andBool(flatten_label('_andBool_', requires))
    requires = simplify_bool(requires)

    ensures = andBool(flatten_label('_andBool_', ensures))
    ensures = simplify_bool(ensures)

    constrained_vars = set(keep_vars) | free_vars(requires) | free_vars(ensures)
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


def remove_generated_cells(term: KInner) -> KInner:
    """Remove <generatedTop> and <generatedCounter> from a configuration.

    Args:
        term: A term.

    Returns:
        The term with those cells removed.
    """
    rewrite = KRewrite(KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG'))
    return rewrite(term)


def is_anon_var(kast: KInner) -> bool:
    return type(kast) is KVariable and kast.name.startswith('_')


def set_cell(constrained_term: KInner, cell_variable: str, cell_value: KInner) -> KInner:
    state, constraint = split_config_and_constraints(constrained_term)
    config, subst = split_config_from(state)
    subst[cell_variable] = cell_value
    return mlAnd([Subst(subst)(config), constraint])


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


def apply_existential_substitutions(state: KInner, constraints: Iterable[KInner]) -> tuple[KInner, Iterable[KInner]]:
    pattern = mlEqualsTrue(KApply('_==K_', [KVariable('#VAR'), KVariable('#VAL')]))
    subst = {}
    new_constraints = []
    for c in constraints:
        match = pattern.match(c)
        if match is not None and type(match['#VAR']) is KVariable and match['#VAR'].name.startswith('?'):
            subst[match['#VAR'].name] = match['#VAL']
        else:
            new_constraints.append(c)
    return (Subst(subst)(state), [Subst(subst)(c) for c in new_constraints])


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


def is_spurious_constraint(term: KInner) -> bool:
    if type(term) is KApply and term.label.name == '#Equals' and term.args[0] == term.args[1]:
        return True
    if is_top(term, weak=True):
        return True
    return False


def normalize_constraints(constraints: Iterable[KInner]) -> tuple[KInner, ...]:
    constraints = (constraint for _constraint in constraints for constraint in flatten_label('#And', _constraint))
    constraints = unique(constraints)
    constraints = (constraint for constraint in constraints if not is_spurious_constraint(constraint))
    return tuple(constraints)


def remove_useless_constraints(constraints: Iterable[KInner], initial_vars: Iterable[str]) -> list[KInner]:
    """Remove constraints that do not depend on a given iterable of variables (directly or indirectly).

    Args:
        constraints: Iterable of constraints to filter.
        initial_vars: Initial iterable of variables to keep constraints for.

    Returns:
        A list of constraints with only those constraints that contain the initial variables,
        or variables that depend on those through other constraints in the list.
    """
    used_vars = list(initial_vars)
    prev_len_used_vars = 0
    new_constraints = []
    while len(used_vars) > prev_len_used_vars:
        prev_len_used_vars = len(used_vars)
        for c in constraints:
            if c not in new_constraints:
                new_vars = free_vars(c)
                if any(v in used_vars for v in new_vars):
                    new_constraints.append(c)
                    used_vars.extend(new_vars)
        used_vars = list(set(used_vars))
    return new_constraints


def build_claim(
    claim_id: str,
    init_config: KInner,
    final_config: KInner,
    init_constraints: Iterable[KInner] = (),
    final_constraints: Iterable[KInner] = (),
    keep_vars: Iterable[str] = (),
) -> tuple[KClaim, Subst]:
    """Return a `KClaim` between the supplied initial and final states.

    Args:
        claim_id: Label to give the claim.
        init_config: State to put on LHS of the rule.
        final_config: State to put on RHS of the rule.
        init_constraints: Constraints to use as `requires` clause.
        final_constraints: Constraints to use as `ensures` clause.
        keep_vars: Variables to leave in the side-conditions even if not bound in the configuration.

    Returns:
        A tuple ``(claim, var_map)`` where

        - ``claim``: A `KClaim` with variable naming conventions applied
          so that it should be parseable by the K Frontend.
        - ``var_map``: The variable renamings applied to make the claim parseable by the K Frontend
          (which can be undone to recover the original variables).
    """
    rule, var_map = build_rule(
        claim_id, init_config, final_config, init_constraints, final_constraints, keep_vars=keep_vars
    )
    claim = KClaim(rule.body, requires=rule.requires, ensures=rule.ensures, att=rule.att)
    return claim, var_map


def build_rule(
    rule_id: str,
    init_config: KInner,
    final_config: KInner,
    init_constraints: Iterable[KInner] = (),
    final_constraints: Iterable[KInner] = (),
    priority: int | None = None,
    keep_vars: Iterable[str] = (),
    defunc_with: KDefinition | None = None,
) -> tuple[KRule, Subst]:
    """Return a `KRule` between the supplied initial and final states.

    Args:
        rule_id: Label to give the rule.
        init_config: State to put on LHS of the rule.
        final_config: State to put on RHS of the rule.
        init_constraints: Constraints to use as `requires` clause.
        final_constraints: Constraints to use as `ensures` clause.
        priority: Priority index to assign to generated rules.
        keep_vars: Variables to leave in the side-conditions even if not bound in the configuration.
        defunc_with: KDefinition for filtering out function symbols on LHS of rules.

    Returns:
        A tuple ``(rule, var_map)`` where

        - ``rule``: A `KRule` with variable naming conventions applied
          so that it should be parseable by the K Frontend.
        - ``var_map``: The variable renamings applied to make the rule parseable by the K Frontend
          (which can be undone to recover the original variables).
    """
    init_constraints = [normalize_ml_pred(c) for c in init_constraints]
    final_constraints = [normalize_ml_pred(c) for c in final_constraints]
    final_constraints = [c for c in final_constraints if c not in init_constraints]
    if defunc_with is not None:
        init_config, new_constraints = defunctionalize(defunc_with, init_config)
        init_constraints = init_constraints + new_constraints
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

    new_init_config = Subst(v_subst)(init_config)
    new_init_constraints = [Subst(v_subst)(c) for c in init_constraints]
    new_final_config, new_final_constraints = apply_existential_substitutions(
        Subst(v_subst)(final_config), [Subst(v_subst)(c) for c in final_constraints]
    )

    rule_body = push_down_rewrites(KRewrite(new_init_config, new_final_config))
    rule_requires = simplify_bool(ml_pred_to_bool(mlAnd(new_init_constraints)))
    rule_ensures = simplify_bool(ml_pred_to_bool(mlAnd(new_final_constraints)))
    att_entries = [] if priority is None else [Atts.PRIORITY(str(priority))]
    rule_att = KAtt(entries=att_entries)

    rule = KRule(rule_body, requires=rule_requires, ensures=rule_ensures, att=rule_att)
    rule = rule.update_atts([Atts.LABEL(rule_id)])

    return (rule, Subst(vremap_subst))


def replace_rewrites_with_implies(kast: KInner) -> KInner:
    def _replace_rewrites_with_implies(_kast: KInner) -> KInner:
        if type(_kast) is KRewrite:
            return mlImplies(_kast.lhs, _kast.rhs)
        return _kast

    return bottom_up(_replace_rewrites_with_implies, kast)


def no_cell_rewrite_to_dots(term: KInner) -> KInner:
    """Transform a given term by replacing the contents of each cell with dots if the LHS and RHS are the same.

    This function recursively traverses the cells in a term.
    When it finds a cell whose left-hand side (LHS) is identical to its right-hand side (RHS),
    it replaces the cell's contents with a predefined DOTS.

    Args:
        term: The term to be transformed.

    Returns:
        The transformed term, where specific cell contents have been replaced with dots.
    """

    def _no_cell_rewrite_to_dots(_term: KInner) -> KInner:
        if type(_term) is KApply and _term.is_cell:
            lhs = extract_lhs(_term)
            rhs = extract_rhs(_term)
            if lhs == rhs:
                return KApply(_term.label, [DOTS])
        return _term

    config, _subst = split_config_from(term)
    subst = Subst({cell_name: _no_cell_rewrite_to_dots(cell_contents) for cell_name, cell_contents in _subst.items()})

    return subst(config)


def defunctionalize(defn: KDefinition, kinner: KInner) -> tuple[KInner, list[KInner]]:
    """Turn non-constructor arguments into side-conditions so that a term is only constructor-like.

    Args:
        defn: The definition to pull function label information from.
        kinner: The term to defunctionalize.

    Returns:
        A tuple of the defunctionalized term and the list of constraints generated.
    """
    function_symbols = [prod.klabel for prod in defn.functions if prod.klabel is not None]
    constraints: list[KInner] = []

    def _defunctionalize(_kinner: KInner) -> KInner:
        if type(_kinner) is KApply and _kinner.label in function_symbols:
            sort = defn.sort(_kinner)
            assert sort is not None
            new_var = abstract_term_safely(_kinner, base_name='F', sort=sort)
            var_constraint = mlEquals(new_var, _kinner, arg_sort=sort)
            constraints.append(var_constraint)
            return new_var
        return _kinner

    new_kinner = top_down(_defunctionalize, kinner)
    return (new_kinner, list(unique(constraints)))
