from __future__ import annotations

import logging
from functools import reduce
from typing import TYPE_CHECKING

from ..kast import Atts
from ..kast.inner import KApply, KLabel, KSequence, KSort, KToken, KVariable, top_down
from ..kast.manip import bool_to_ml_pred, extract_lhs, extract_rhs, flatten_label
from ..kast.outer import KRule
from ..kore.prelude import SORT_K
from ..kore.syntax import DV, And, App, Axiom, EVar, Import, MLPattern, MLQuant, Module, Rewrites, SortApp, String, Top
from ..prelude.bytes import BYTES, pretty_bytes_str
from ..prelude.k import K_ITEM, K, inj
from ..prelude.kbool import TRUE
from ..prelude.ml import mlAnd
from ..prelude.string import STRING, pretty_string
from ._utils import munge

if TYPE_CHECKING:
    from typing import Final

    from ..kast import KInner
    from ..kast.outer import KDefinition, KFlatModule, KImport
    from ..kore.syntax import Pattern, Sentence, Sort

_LOGGER: Final = logging.getLogger(__name__)


ML_CONN_LABELS: Final = {
    '#Top': r'\top',
    '#Bottom': r'\bottom',
    '#Not': r'\not',
    '#And': r'\and',
    '#Or': r'\or',
    '#Implies': r'\implies',
    '#Iff': r'\iff',
}

ML_QUANT_LABELS: Final = {
    '#Exists': r'\exists',
    '#Forall': r'\forall',
}

ML_PRED_LABELS: Final = {
    '#Ceil': r'\ceil',
    '#Floor': r'\floor',
    '#Equals': r'\equals',
    '#In': r'\in',
}

ML_PATTERN_LABELS: Final = dict(
    **ML_CONN_LABELS,
    **ML_QUANT_LABELS,
    **ML_PRED_LABELS,
)


def kast_to_kore(definition: KDefinition, kast: KInner, sort: KSort | None = None) -> Pattern:
    sort = sort or K
    kast = definition.add_ksequence_under_k_productions(kast)
    kast = definition.sort_vars(kast, sort)
    kast = definition.add_cell_map_items(kast)
    kast = definition.add_sort_params(kast)
    kast = _replace_ksequence_by_kapply(kast)
    kast = _add_sort_injections(definition, kast, sort)
    kore = _kast_to_kore(kast)
    return kore


def _replace_ksequence_by_kapply(term: KInner) -> KInner:
    dotk = KApply('dotk')
    kseq = KLabel('kseq')

    def transform(term: KInner) -> KInner:
        match term:
            case KSequence(items):
                return transform_items(items)
            case _:
                return term

    def transform_items(items: tuple[KInner, ...]) -> KInner:
        if not items:
            return dotk

        unit: KInner
        args: tuple[KInner, ...]

        last = items[-1]
        if isinstance(last, KVariable) and last.sort == K:
            unit = last
            args = items[:-1]
        else:
            unit = dotk
            args = items

        return reduce(lambda x, y: kseq(y, x), reversed(args), unit)

    return top_down(transform, term)


def _add_sort_injections(definition: KDefinition, term: KInner, sort: KSort) -> KInner:
    """Add sort injections to a KAST term bottom-up.

    Maintains its own stack for an iterative implementation. Each stack frame consists of:
    - `term`: the current term
    - `sort`: the sort the current term must be injected to
    - `argument_terms`: direct subterms of the current term
    - `argument_sorts`: the sorts the respective direct subterms must be injected to
    - `done_terms`: results for direct subterms
    """
    stack: list = [term, sort, _argument_terms(definition, term), _argument_sorts(definition, term), []]
    while True:
        done_terms = stack[-1]
        argument_sorts = stack[-2]
        argument_terms = stack[-3]
        sort = stack[-4]
        term = stack[-5]

        idx = len(done_terms) - len(argument_terms)
        if not idx:
            stack.pop()
            stack.pop()
            stack.pop()
            stack.pop()
            stack.pop()
            term = _let_arguments(term, done_terms)
            term = _inject(definition, term, sort)
            if not stack:
                return term
            stack[-1].append(term)
        else:
            term = argument_terms[idx]
            stack.append(term)
            stack.append(argument_sorts[idx])
            stack.append(_argument_terms(definition, term))
            stack.append(_argument_sorts(definition, term))
            stack.append([])


def _argument_terms(definition: KDefinition, term: KInner) -> tuple[KInner, ...]:
    match term:
        case KApply(KLabel('#Exists' | '#Forall')):  # Special case: ML quantifiers
            _, term = term.args
            return (term,)
        case _:
            return term.terms


def _argument_sorts(definition: KDefinition, term: KInner) -> tuple[KSort, ...]:
    match term:
        case KToken() | KVariable():
            return ()
        case KSequence(items):
            return len(items) * (K_ITEM,)
        case KApply(KLabel(name)):
            match name:
                case 'kseq':
                    return (K_ITEM, K)
                case 'dotk':
                    return ()
                case '#Forall' | '#Exists':
                    _, argument_sorts = definition.resolve_sorts(term.label)
                    _, argument_sort = argument_sorts
                    return (argument_sort,)
                case _:
                    _, argument_sorts = definition.resolve_sorts(term.label)
                    return argument_sorts
        case _:
            raise ValueError(f'Unsupported term: {term}')


def _let_arguments(term: KInner, args: list[KInner]) -> KInner:
    match term:
        case KApply(KLabel('#Exists' | '#Forall')):  # Special case: ML quantifiers
            args = [term.args[0]] + args
            return term.let_terms(args)
        case _:
            return term.let_terms(args)


def _inject(definition: KDefinition, term: KInner, sort: KSort) -> KInner:
    actual_sort: KSort
    match term:
        case KApply(KLabel('kseq' | 'dotk')):  # Special case: pseudo-labels
            actual_sort = K
        case _:
            actual_sort = definition.sort_strict(term)

    if actual_sort == sort:
        return term

    if actual_sort in definition.subsorts(sort):
        return inj(from_sort=actual_sort, to_sort=sort, term=term)

    raise ValueError(f'Sort {actual_sort.name} is not a subsort of {sort.name}: {term}')


# 'krule' should have sorts on variables
def krule_to_kore(definition: KDefinition, krule: KRule) -> Axiom:
    krule_body = krule.body
    krule_lhs_config = extract_lhs(krule_body)
    krule_rhs_config = extract_rhs(krule_body)
    krule_lhs_constraints = [bool_to_ml_pred(c) for c in flatten_label('_andBool_', krule.requires) if not c == TRUE]
    krule_rhs_constraints = [bool_to_ml_pred(c) for c in flatten_label('_andBool_', krule.ensures) if not c == TRUE]
    krule_lhs = mlAnd([krule_lhs_config] + krule_lhs_constraints)
    krule_rhs = mlAnd([krule_rhs_config] + krule_rhs_constraints)

    top_level_kore_sort = SortApp('SortGeneratedTopCell')
    top_level_k_sort = KSort('GeneratedTopCell')
    # The backend does not like rewrite rules without a precondition
    if len(krule_lhs_constraints) > 0:
        kore_lhs: Pattern = kast_to_kore(definition, krule_lhs, sort=top_level_k_sort)
    else:
        kore_lhs = And(
            top_level_kore_sort,
            (
                kast_to_kore(definition, krule_lhs, sort=top_level_k_sort),
                Top(top_level_kore_sort),
            ),
        )

    kore_rhs: Pattern = kast_to_kore(definition, krule_rhs, sort=top_level_k_sort)

    prio = krule.priority
    attrs = [App(symbol='priority', sorts=(), args=(String(str(prio)),))]
    if Atts.LABEL in krule.att:
        label = krule.att[Atts.LABEL]
        attrs.append(App(symbol='label', sorts=(), args=(String(label),)))
    axiom = Axiom(
        vars=(),
        pattern=Rewrites(
            sort=top_level_kore_sort,
            left=kore_lhs,
            right=kore_rhs,
        ),
        attrs=attrs,
    )
    return axiom


def kflatmodule_to_kore(definition: KDefinition, kflatmodule: KFlatModule) -> Module:
    kore_axioms: list[Sentence] = []
    for sent in kflatmodule.sentences:
        if type(sent) is not KRule:
            raise ValueError(f'Cannot convert sentence to Kore: {sent}')
        kore_axioms.append(krule_to_kore(definition, sent))
    imports: list[Sentence] = [_kimport_to_kore(kimport) for kimport in kflatmodule.imports]
    return Module(name=kflatmodule.name, sentences=(imports + kore_axioms))


def _kimport_to_kore(kimport: KImport) -> Import:
    return Import(module_name=kimport.name, attrs=())


def _ksort_to_kore(ksort: KSort) -> SortApp:
    return SortApp('Sort' + ksort.name)


def _kast_to_kore(term: KInner) -> Pattern:
    stack: list = [term, []]
    while True:
        patterns = stack[-1]
        term = stack[-2]
        idx = len(patterns) - len(term.terms)
        if not idx:
            stack.pop()
            stack.pop()
            pattern = _kinner_to_kore(term, patterns)
            if not stack:
                return pattern
            stack[-1].append(pattern)
        else:
            stack.append(term.terms[idx])
            stack.append([])


def _kinner_to_kore(kinner: KInner, patterns: list[Pattern]) -> Pattern:
    match kinner:
        case KToken():
            assert not patterns
            return _ktoken_to_kore(kinner)
        case KVariable():
            assert not patterns
            return _kvariable_to_kore(kinner)
        case KApply():
            return _kapply_to_kore(kinner, patterns)
        case _:
            raise ValueError(f'Unsupported KInner: {kinner}')


def _ktoken_to_kore(ktoken: KToken) -> DV:
    value: String
    if ktoken.sort == STRING:
        value = String(pretty_string(ktoken))
    elif ktoken.sort == BYTES:
        value = String(pretty_bytes_str(ktoken))
    else:
        value = String(ktoken.token)

    sort = _ksort_to_kore(ktoken.sort)

    return DV(sort, value)


def _kvariable_to_kore(kvar: KVariable) -> EVar:
    sort: Sort
    if kvar.sort:
        sort = _ksort_to_kore(kvar.sort)
    else:
        sort = SORT_K
    return EVar('Var' + munge(kvar.name), sort)


def _kapply_to_kore(kapply: KApply, patterns: list[Pattern]) -> Pattern:
    if kapply.label.name in ML_QUANT_LABELS:
        return _kapply_to_ml_quant(kapply, patterns)

    return _kapply_to_pattern(kapply, patterns)


def _kapply_to_ml_quant(kapply: KApply, patterns: list[Pattern]) -> MLQuant:
    label = kapply.label
    symbol = ML_QUANT_LABELS[label.name]
    _, ksort = label.params
    sort = _ksort_to_kore(ksort)
    return MLQuant.of(symbol, (sort,), patterns)


def _kapply_to_pattern(kapply: KApply, patterns: list[Pattern]) -> Pattern:
    label = kapply.label
    symbol = _label_to_kore(label.name)
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)

    if label.name in ML_PATTERN_LABELS:
        return MLPattern.of(symbol, sorts, patterns)

    return App(symbol, sorts, patterns)


def _label_to_kore(label: str) -> str:
    if label in ['inj', 'kseq', 'dotk']:  # pseudo-labels introduced during KAST-to-KORE tranformation
        return label

    if label in ML_PATTERN_LABELS:
        return ML_PATTERN_LABELS[label]

    return 'Lbl' + munge(label)
