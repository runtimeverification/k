from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..kast.inner import KApply, KLabel, KSequence, KSort, KToken, KVariable
from ..kore.prelude import BYTES as KORE_BYTES
from ..kore.prelude import LBL_ITE
from ..kore.prelude import STRING as KORE_STRING
from ..kore.syntax import (
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
    Not,
    Or,
    SortApp,
    String,
    Top,
)
from ..prelude.bytes import bytesToken_from_str
from ..prelude.ml import mlAnd, mlBottom, mlCeil, mlEquals, mlExists, mlImplies, mlNot, mlOr, mlTop
from ..prelude.string import stringToken
from ._utils import unmunge

if TYPE_CHECKING:
    from typing import Final

    from ..kast import KInner
    from ..kast.outer import KDefinition
    from ..kore.syntax import Pattern, Sort

_LOGGER: Final = logging.getLogger(__name__)


def kore_to_kast(kast_defn: KDefinition, kore: Pattern) -> KInner:
    kast = _kore_to_kast(kore)
    return kast_defn.remove_cell_map_items(kast)


def _kore_to_kast(pattern: Pattern) -> KInner:
    stack: list = [pattern.pattern if isinstance(pattern, Assoc) else pattern, []]
    while True:
        terms = stack[-1]
        pattern = stack[-2]
        patterns = pattern.patterns
        idx = len(terms) - len(patterns)
        if not idx:
            stack.pop()
            stack.pop()
            term = _pattern_to_kast(pattern, terms)
            if not stack:
                return term
            stack[-1].append(term)
        else:
            pattern = patterns[idx]
            stack.append(pattern.pattern if isinstance(pattern, Assoc) else pattern)
            stack.append([])


def _pattern_to_kast(pattern: Pattern, terms: list[KInner]) -> KInner:
    match pattern:
        case DV(sort, String(value)):
            assert not terms
            if sort == KORE_STRING:
                return stringToken(value)
            if sort == KORE_BYTES:
                return bytesToken_from_str(value)
            return KToken(value, _sort_to_kast(sort))

        case EVar(name, sort):
            assert not terms
            return KVariable(name=unmunge(name[3:]), sort=_sort_to_kast(sort))

        case App(symbol, sorts, _):
            if symbol == 'inj':
                _, _ = sorts
                (term,) = terms
                return term

            elif not sorts:
                if symbol == 'dotk':
                    () = terms
                    return KSequence(())

                elif symbol == 'kseq':
                    _, _ = terms
                    return KSequence(terms)

                else:
                    klabel = KLabel(unmunge(symbol[3:]))
                    return KApply(klabel, terms)

            # hardcoded polymorphic operators
            elif symbol == LBL_ITE.value:
                (sort,) = sorts
                klabel = KLabel(unmunge(symbol[3:]), (_sort_to_kast(sort),))
                return KApply(klabel, terms)

            else:
                raise ValueError(f'Unsupported polymorphic operator: {symbol}')

        case Top(sort):
            assert not terms
            return mlTop(sort=_sort_to_kast(sort))

        case Bottom(sort):
            assert not terms
            return mlBottom(sort=_sort_to_kast(sort))

        case And(sort, _):
            return mlAnd(terms, sort=_sort_to_kast(sort))

        case Or(sort, _):
            return mlOr(terms, sort=_sort_to_kast(sort))

        case Implies(sort, _, _):
            larg, rarg = terms
            return mlImplies(larg, rarg, sort=_sort_to_kast(sort))

        case Not(sort, _):
            (karg,) = terms
            return mlNot(karg, sort=_sort_to_kast(sort))

        case Exists(sort, EVar(vname, vsort), _):
            ksort = _sort_to_kast(sort)
            kvsort = _sort_to_kast(vsort)
            kvar = KVariable(name=unmunge(vname[3:]), sort=kvsort)
            (body,) = terms
            return mlExists(kvar, body, sort1=kvsort, sort2=ksort)

        case Equals(op_sort, sort, _, _):
            larg, rarg = terms
            return mlEquals(
                larg,
                rarg,
                arg_sort=_sort_to_kast(op_sort),
                sort=_sort_to_kast(sort),
            )

        case Ceil(op_sort, sort, _):
            (karg,) = terms
            return mlCeil(
                karg,
                arg_sort=_sort_to_kast(op_sort),
                sort=_sort_to_kast(sort),
            )

        case _:
            raise ValueError(f'Unsupported Pattern: {pattern}')


def _sort_to_kast(sort: Sort) -> KSort:
    if not isinstance(sort, SortApp) or not sort.name.startswith('Sort'):
        raise ValueError(f'Unsupported Sort: {sort}')
    return KSort(sort.name[4:])
