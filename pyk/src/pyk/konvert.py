from __future__ import annotations

import logging
from functools import reduce
from typing import TYPE_CHECKING

from .kast.inner import KApply, KLabel, KSequence, KSort, KToken, KVariable
from .kore.prelude import BYTES as KORE_BYTES
from .kore.prelude import STRING as KORE_STRING
from .kore.syntax import (
    DV,
    And,
    App,
    Assoc,
    Bottom,
    Ceil,
    Equals,
    EVar,
    Exists,
    Implies,
    MLPattern,
    MLQuant,
    Not,
    SortApp,
    String,
    Top,
)
from .prelude.bytes import BYTES, bytesToken, pretty_bytes
from .prelude.k import K
from .prelude.ml import mlAnd, mlBottom, mlCeil, mlEquals, mlExists, mlImplies, mlNot, mlTop
from .prelude.string import STRING, pretty_string, stringToken
from .utils import FrozenDict

if TYPE_CHECKING:
    from typing import Final

    from .kast import KInner
    from .kast.outer import KDefinition
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
    kast = kast_defn.sort_vars(kast, sort)
    kast = kast_defn.add_cell_map_items(kast)
    kore = _kast_to_kore(kast)
    return kompiled_kore.add_injections(kore, _ksort_to_kore(sort))


def _kast_to_kore(kast: KInner) -> Pattern:
    _LOGGER.debug(f'_kast_to_kore: {kast}')
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
        value = String(pretty_bytes(ktoken))
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
            return bytesToken(kore.value.value)
        return KToken(kore.value.value, KSort(kore.sort.name[4:]))

    elif type(kore) is EVar:
        vname = unmunge(kore.name[3:])
        return KVariable(vname, sort=KSort(kore.sort.name[4:]))

    elif type(kore) is App:
        if kore.symbol == 'inj' and len(kore.sorts) == 2 and len(kore.args) == 1:
            return _kore_to_kast(kore.args[0])

        elif len(kore.sorts) == 0:
            if kore.symbol == 'dotk' and len(kore.args) == 0:
                return KSequence([])

            elif kore.symbol == 'kseq' and len(kore.args) == 2:
                p0 = _kore_to_kast(kore.args[0])
                p1 = _kore_to_kast(kore.args[1])
                if p0 is not None and p1 is not None:
                    return KSequence([p0, p1])

            else:
                _label_name = unmunge(kore.symbol[3:])
                klabel = KLabel(_label_name, [KSort(k.name[4:]) for k in kore.sorts])
                args = [_kore_to_kast(_a) for _a in kore.args]
                # TODO: Written like this to appease the type-checker.
                new_args = [a for a in args if a is not None]
                if len(new_args) == len(args):
                    return KApply(klabel, new_args)

        # hardcoded polymorphic operators
        elif (
            len(kore.sorts) == 1
            and kore.symbol
            == "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort"
        ):
            _label_name = unmunge(kore.symbol[3:])
            klabel = KLabel(_label_name, [KSort(kore.sorts[0].name[4:])])
            # TODO: Written like this to appease the type-checker.
            args = [_kore_to_kast(_a) for _a in kore.args]
            new_args = [a for a in args if a is not None]
            if len(new_args) == len(args):
                return KApply(klabel, new_args)

    elif type(kore) is Top:
        return mlTop(sort=KSort(kore.sort.name[4:]))

    elif type(kore) is Bottom:
        return mlBottom(sort=KSort(kore.sort.name[4:]))

    elif type(kore) is And:
        psort = KSort(kore.sort.name[4:])
        larg = _kore_to_kast(kore.left)
        rarg = _kore_to_kast(kore.right)
        if larg is not None and rarg is not None:
            return mlAnd([larg, rarg], sort=psort)

    elif type(kore) is Implies:
        psort = KSort(kore.sort.name[4:])
        larg = _kore_to_kast(kore.left)
        rarg = _kore_to_kast(kore.right)
        if larg is not None and rarg is not None:
            return mlImplies(larg, rarg, sort=psort)

    elif type(kore) is Not:
        psort = KSort(kore.sort.name[4:])
        arg = _kore_to_kast(kore.pattern)
        if arg is not None:
            return mlNot(arg, sort=psort)

    elif type(kore) is Exists:
        psort = KSort(kore.sort.name[4:])
        var = _kore_to_kast(kore.var)
        body = _kore_to_kast(kore.pattern)
        if var is not None and body is not None:
            assert type(var) is KVariable
            return mlExists(var, body, sort=psort)

    elif type(kore) is Equals:
        osort = KSort(kore.op_sort.name[4:])
        psort = KSort(kore.sort.name[4:])
        larg = _kore_to_kast(kore.left)
        rarg = _kore_to_kast(kore.right)
        if larg is not None and rarg is not None:
            return mlEquals(larg, rarg, arg_sort=osort, sort=psort)

    elif type(kore) is Ceil:
        osort = KSort(kore.op_sort.name[4:])
        psort = KSort(kore.sort.name[4:])
        arg = _kore_to_kast(kore.pattern)
        if arg is not None:
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


class Unmunger:
    _rest: str

    def __init__(self, symbol: str):
        self._rest = symbol

    def label(self) -> str:
        res = ''
        while self._la():
            if self._la() == "'":
                self._consume()
                res += self._unmunged()
                while self._la() != "'":
                    res += self._unmunged()
                self._consume()
                if self._la() == "'":
                    raise ValueError('Quoted sections next to each other')
            else:
                res += self._consume()
        return res

    def _la(self) -> str | None:
        if self._rest:
            return self._rest[0]
        return None

    def _consume(self, n: int = 1) -> str:
        if len(self._rest) < n:
            raise ValueError('Unexpected end of symbol')
        consumed = self._rest[:n]
        self._rest = self._rest[n:]
        return consumed

    def _unmunged(self) -> str:
        munged = self._consume(4)
        if munged not in UNMUNGE_TABLE:
            raise ValueError(f'Unknown encoding "{munged}"')
        return UNMUNGE_TABLE[munged]


def unmunge(symbol: str) -> str:
    return Unmunger(symbol).label()
