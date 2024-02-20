from __future__ import annotations

import logging
from functools import reduce
from typing import TYPE_CHECKING

from ..cterm import CTerm
from ..kast import Atts
from ..kast.inner import KApply, KSequence, KSort, KToken, KVariable
from ..kast.manip import bool_to_ml_pred, extract_lhs, extract_rhs
from ..kast.outer import KRule
from ..kore.prelude import DOTK, SORT_K
from ..kore.syntax import DV, And, App, Axiom, EVar, Import, MLPattern, MLQuant, Module, Rewrites, SortApp, String, Top
from ..prelude.bytes import BYTES, pretty_bytes_str
from ..prelude.k import K
from ..prelude.string import STRING, pretty_string
from ._utils import munge

if TYPE_CHECKING:
    from typing import Final

    from ..kast import KInner
    from ..kast.outer import KDefinition, KFlatModule, KImport
    from ..kore.kompiled import KompiledKore
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


def kast_to_kore(
    kast_defn: KDefinition,
    kompiled_kore: KompiledKore,
    kast: KInner,
    sort: KSort | None = None,
) -> Pattern:
    if sort is None:
        sort = K
    kast = kast_defn.add_ksequence_under_k_productions(kast)
    kast = kast_defn.sort_vars(kast, sort)
    kast = kast_defn.add_cell_map_items(kast)
    kast = kast_defn.add_sort_params(kast)
    kore = _kast_to_kore(kast)
    kore = kompiled_kore.add_injections(kore, _ksort_to_kore(sort))
    return kore


# 'krule' should have sorts on variables
def krule_to_kore(kast_defn: KDefinition, kompiled_kore: KompiledKore, krule: KRule) -> Axiom:
    krule_body = krule.body
    krule_lhs = CTerm(extract_lhs(krule_body), [bool_to_ml_pred(krule.requires)])
    krule_rhs = CTerm(extract_rhs(krule_body), [bool_to_ml_pred(krule.ensures)])

    top_level_kore_sort = SortApp('SortGeneratedTopCell')
    top_level_k_sort = KSort('GeneratedTopCell')
    # The backend does not like rewrite rules without a precondition
    if len(krule_lhs.constraints) > 0:
        kore_lhs0: Pattern = kast_to_kore(kast_defn, kompiled_kore, krule_lhs.kast, sort=top_level_k_sort)
    else:
        kore_lhs0 = And(
            top_level_kore_sort,
            (
                kast_to_kore(kast_defn, kompiled_kore, krule_lhs.kast, sort=top_level_k_sort),
                Top(top_level_kore_sort),
            ),
        )

    kore_rhs0: Pattern = kast_to_kore(kast_defn, kompiled_kore, krule_rhs.kast, sort=top_level_k_sort)

    kore_lhs = kompiled_kore.add_injections(kore_lhs0, sort=top_level_kore_sort)
    kore_rhs = kompiled_kore.add_injections(kore_rhs0, sort=top_level_kore_sort)
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


def kflatmodule_to_kore(kast_defn: KDefinition, kompiled_kore: KompiledKore, kflatmodule: KFlatModule) -> Module:
    kore_axioms: list[Sentence] = []
    for sent in kflatmodule.sentences:
        if type(sent) is not KRule:
            raise ValueError(f'Cannot convert sentence to Kore: {sent}')
        kore_axioms.append(krule_to_kore(kast_defn, kompiled_kore, sent))
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
        case KSequence():
            return _ksequence_to_kore(kinner, patterns)
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


def _ksequence_to_kore(kseq: KSequence, patterns: list[Pattern]) -> Pattern:
    if not patterns:
        return DOTK

    unit: Pattern
    args: list[Pattern]

    last = patterns[-1]
    if type(last) is EVar and last.sort == SORT_K:
        unit = last
        args = patterns[:-1]
    else:
        unit = DOTK
        args = patterns

    args.reverse()
    return reduce(lambda x, y: App('kseq', (), (y, x)), args, unit)


def _kapply_to_kore(kapply: KApply, patterns: list[Pattern]) -> Pattern:
    if kapply.label.name in ML_QUANT_LABELS:
        return _kapply_to_ml_quant(kapply, patterns)

    return _kapply_to_pattern(kapply, patterns)


def _kapply_to_ml_quant(kapply: KApply, patterns: list[Pattern]) -> MLQuant:
    label = kapply.label
    symbol = ML_QUANT_LABELS[label.name]
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)
    return MLQuant.of(symbol, sorts, patterns)


def _kapply_to_pattern(kapply: KApply, patterns: list[Pattern]) -> Pattern:
    label = kapply.label
    symbol = _label_to_kore(label.name)
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)

    if label.name in ML_PATTERN_LABELS:
        return MLPattern.of(symbol, sorts, patterns)

    return App(symbol, sorts, patterns)


def _label_to_kore(label: str) -> str:
    if label in ML_PATTERN_LABELS:
        return ML_PATTERN_LABELS[label]

    return 'Lbl' + munge(label)
