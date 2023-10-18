from __future__ import annotations

import logging
from functools import reduce
from typing import TYPE_CHECKING

from .cterm import CTerm
from .kast.inner import KApply, KLabel, KSequence, KSort, KToken, KVariable
from .kast.manip import bool_to_ml_pred, extract_lhs, extract_rhs
from .kore.prelude import BYTES as KORE_BYTES
from .kore.prelude import STRING as KORE_STRING
from .kore.syntax import (
    DV,
    And,
    App,
    Assoc,
    Axiom,
    Bottom,
    Ceil,
    Equals,
    EVar,
    Exists,
    Implies,
    MLPattern,
    MLQuant,
    Not,
    Rewrites,
    SortApp,
    String,
    Top,
)
from .prelude.bytes import BYTES, bytesToken_from_str, pretty_bytes_str
from .prelude.k import K
from .prelude.ml import mlAnd, mlBottom, mlCeil, mlEquals, mlExists, mlImplies, mlNot, mlTop
from .prelude.string import STRING, pretty_string, stringToken
from .utils import FrozenDict

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Final

    from .kast import KInner
    from .kast.outer import KDefinition, KRule
    from .kore.kompiled import KompiledKore
    from .kore.syntax import Pattern, Sort

_LOGGER: Final = logging.getLogger(__name__)

# ------------
# KAST-to-KORE
# ------------

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
    if 'label' in krule.att:
        label = krule.att['label']
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


def _kast_to_kore(kast: KInner) -> Pattern:
    if type(kast) is KToken:
        return _ktoken_to_kore(kast)
    elif type(kast) is KVariable:
        return _kvariable_to_kore(kast)
    elif type(kast) is KSequence:
        return _ksequence_to_kore(kast)
    elif type(kast) is KApply:
        return _kapply_to_kore(kast)

    raise ValueError(f'Unsupported KInner: {kast}')


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


def _ksort_to_kore(ksort: KSort) -> SortApp:
    return SortApp('Sort' + ksort.name)


def _kvariable_to_kore(kvar: KVariable) -> EVar:
    sort: Sort
    if kvar.sort:
        sort = _ksort_to_kore(kvar.sort)
    else:
        sort = SortApp('SortK')
    return EVar('Var' + munge(kvar.name), sort)


def _ksequence_to_kore(kseq: KSequence) -> Pattern:
    if not kseq:
        return App('dotk')

    unit: Pattern
    items: tuple[KInner, ...]

    last = kseq[-1]
    if type(last) is KVariable and (not last.sort or last.sort == KSort('K')):
        unit = _kvariable_to_kore(last)
        items = kseq[:-1]
    else:
        unit = App('dotk')
        items = kseq.items

    patterns = tuple(_kast_to_kore(item) for item in items)
    return reduce(lambda x, y: App('kseq', (), (y, x)), reversed(patterns), unit)


def _kapply_to_kore(kapply: KApply) -> Pattern:
    if kapply.label.name in ML_QUANT_LABELS:
        return _kapply_to_ml_quant(kapply)

    return _kapply_to_pattern(kapply)


def _kapply_to_ml_quant(kapply: KApply) -> MLQuant:
    label = kapply.label
    symbol = ML_QUANT_LABELS[label.name]
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)
    kvar, kast = kapply.args
    var = _kast_to_kore(kvar)
    pattern = _kast_to_kore(kast)
    patterns = (var, pattern)
    return MLQuant.of(symbol, sorts, patterns)


def _kapply_to_pattern(kapply: KApply) -> Pattern:
    label = kapply.label
    symbol = _label_to_kore(label.name)
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)
    patterns = tuple(_kast_to_kore(kast) for kast in kapply.args)

    if label.name in ML_PATTERN_LABELS:
        return MLPattern.of(symbol, sorts, patterns)

    return App(symbol, sorts, patterns)


def _label_to_kore(label: str) -> str:
    if label in ML_PATTERN_LABELS:
        return ML_PATTERN_LABELS[label]

    return 'Lbl' + munge(label)


# ------------
# KORE-to-KAST
# ------------


def kore_to_kast(kast_defn: KDefinition, kore: Pattern) -> KInner:
    kast = _kore_to_kast(kore)
    return kast_defn.remove_cell_map_items(kast)


def _kore_to_kast(kore: Pattern) -> KInner:
    if type(kore) is DV and kore.sort.name.startswith('Sort'):
        if kore.sort == KORE_STRING:
            return stringToken(kore.value.value)
        if kore.sort == KORE_BYTES:
            return bytesToken_from_str(kore.value.value)  # noqa: N802(kore.value.value)
        return KToken(kore.value.value, KSort(kore.sort.name[4:]))

    elif type(kore) is EVar:
        vname = unmunge(kore.name[3:])
        return KVariable(vname, sort=KSort(kore.sort.name[4:]))

    elif type(kore) is App:
        if kore.symbol == 'inj' and len(kore.sorts) == 2 and len(kore.args) == 1:
            return _kore_to_kast(kore.args[0])

        elif len(kore.sorts) == 0:
            if kore.symbol == 'dotk' and len(kore.args) == 0:
                return KSequence(())

            elif kore.symbol == 'kseq' and len(kore.args) == 2:
                p0 = _kore_to_kast(kore.args[0])
                p1 = _kore_to_kast(kore.args[1])
                return KSequence((p0, p1))

            else:
                _label_name = unmunge(kore.symbol[3:])
                klabel = KLabel(_label_name, [KSort(k.name[4:]) for k in kore.sorts])
                args = tuple(_kore_to_kast(_a) for _a in kore.args)
                return KApply(klabel, args)

        # hardcoded polymorphic operators
        elif (
            len(kore.sorts) == 1
            and kore.symbol
            == "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort"
        ):
            _label_name = unmunge(kore.symbol[3:])
            klabel = KLabel(_label_name, [KSort(kore.sorts[0].name[4:])])
            args = tuple(_kore_to_kast(_a) for _a in kore.args)
            return KApply(klabel, args)

    elif type(kore) is Top:
        return mlTop(sort=KSort(kore.sort.name[4:]))

    elif type(kore) is Bottom:
        return mlBottom(sort=KSort(kore.sort.name[4:]))

    elif type(kore) is And:
        psort = KSort(kore.sort.name[4:])
        args = tuple(_kore_to_kast(op) for op in kore.ops)
        return mlAnd(args, sort=psort)

    elif type(kore) is Implies:
        psort = KSort(kore.sort.name[4:])
        larg = _kore_to_kast(kore.left)
        rarg = _kore_to_kast(kore.right)
        return mlImplies(larg, rarg, sort=psort)

    elif type(kore) is Not:
        psort = KSort(kore.sort.name[4:])
        arg = _kore_to_kast(kore.pattern)
        return mlNot(arg, sort=psort)

    elif type(kore) is Exists:
        psort = KSort(kore.sort.name[4:])
        var = _kore_to_kast(kore.var)
        assert type(var) is KVariable
        body = _kore_to_kast(kore.pattern)
        return mlExists(var, body, sort=psort)

    elif type(kore) is Equals:
        osort = KSort(kore.op_sort.name[4:])
        psort = KSort(kore.sort.name[4:])
        larg = _kore_to_kast(kore.left)
        rarg = _kore_to_kast(kore.right)
        return mlEquals(larg, rarg, arg_sort=osort, sort=psort)

    elif type(kore) is Ceil:
        osort = KSort(kore.op_sort.name[4:])
        psort = KSort(kore.sort.name[4:])
        arg = _kore_to_kast(kore.pattern)
        return mlCeil(arg, arg_sort=osort, sort=psort)

    elif isinstance(kore, Assoc):
        return _kore_to_kast(kore.pattern)

    raise ValueError(f'Unsupported Pattern: {kore}')


# --------------
# Symbol munging
# --------------

UNMUNGE_TABLE: Final[FrozenDict[str, str]] = FrozenDict(
    {
        'Spce': ' ',
        'Bang': '!',
        'Quot': '"',
        'Hash': '#',
        'Dolr': '$',
        'Perc': '%',
        'And-': '&',
        'Apos': "'",
        'LPar': '(',
        'RPar': ')',
        'Star': '*',
        'Plus': '+',
        'Comm': ',',
        'Stop': '.',
        'Slsh': '/',
        'Coln': ':',
        'SCln': ';',
        '-LT-': '<',
        'Eqls': '=',
        '-GT-': '>',
        'Ques': '?',
        '-AT-': '@',
        'LSqB': '[',
        'RSqB': ']',
        'Bash': '\\',
        'Xor-': '^',
        'Unds': '_',
        'BQuo': '`',
        'LBra': '{',
        'Pipe': '|',
        'RBra': '}',
        'Tild': '~',
    }
)


MUNGE_TABLE: Final[FrozenDict[str, str]] = FrozenDict({v: k for k, v in UNMUNGE_TABLE.items()})


def munge(label: str) -> str:
    symbol = ''
    quot = False
    for c in label:
        if c in MUNGE_TABLE:
            symbol += "'" if not quot else ''
            symbol += MUNGE_TABLE[c]
            quot = True
        else:
            symbol += "'" if quot else ''
            symbol += c
            quot = False
    symbol += "'" if quot else ''
    return symbol


def unmunge(symbol: str) -> str:
    return ''.join(unmunged(symbol))


def unmunged(it: Iterable[str]) -> Iterator[str]:
    it = iter(it)

    startquote = False
    quote = False
    endquote = False
    buff: list[str] = []
    cnt = 0  # len(buff)

    for c in it:
        if c == "'":
            if startquote:
                raise ValueError('Empty quoted section')
            elif quote:
                if cnt == 0:
                    quote = False
                    endquote = True
                else:
                    fragment = ''.join(buff)
                    raise ValueError(f'Unexpected end of symbol: {fragment}')
            elif endquote:
                raise ValueError('Quoted sections next to each other')
            else:
                quote = True
                startquote = True

        else:
            startquote = False
            endquote = False
            if quote:
                if cnt == 3:
                    buff.append(c)
                    munged = ''.join(buff)
                    buff = []
                    cnt = 0
                    if not munged in UNMUNGE_TABLE:
                        raise ValueError(f'Unknown encoding "{munged}"')
                    yield UNMUNGE_TABLE[munged]
                else:
                    buff += [c]
                    cnt += 1
            else:
                yield c

    if quote:
        raise ValueError('Unterminated quoted section')
