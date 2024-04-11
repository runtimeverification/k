from __future__ import annotations

from typing import TYPE_CHECKING

from ..kast.inner import KApply, KLabel, build_assoc
from .k import GENERATED_TOP_CELL
from .kbool import BOOL, FALSE, TRUE

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from ..kast import KInner
    from ..kast.inner import KSort, KVariable


ML_QUANTIFIERS: Final = {
    '#Exists',
    '#Forall',
}


def is_top(term: KInner) -> bool:
    return isinstance(term, KApply) and term.label.name == '#Top'


def is_bottom(term: KInner) -> bool:
    return isinstance(term, KApply) and term.label.name == '#Bottom'


def mlEquals(  # noqa: N802
    term1: KInner,
    term2: KInner,
    arg_sort: str | KSort = GENERATED_TOP_CELL,
    sort: str | KSort = GENERATED_TOP_CELL,
) -> KApply:
    return KLabel('#Equals', arg_sort, sort)(term1, term2)


def mlEqualsTrue(term: KInner, sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return mlEquals(TRUE, term, arg_sort=BOOL, sort=sort)


def mlEqualsFalse(term: KInner, sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return mlEquals(FALSE, term, arg_sort=BOOL, sort=sort)


def mlTop(sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Top', sort)()


def mlBottom(sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Bottom', sort)()


def mlNot(term: KInner, sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Not', sort)(term)


def mlAnd(conjuncts: Iterable[KInner], sort: str | KSort = GENERATED_TOP_CELL) -> KInner:  # noqa: N802
    return build_assoc(mlTop(sort), KLabel('#And', sort), filter(lambda x: not is_top(x), conjuncts))


def mlOr(disjuncts: Iterable[KInner], sort: str | KSort = GENERATED_TOP_CELL) -> KInner:  # noqa: N802
    return build_assoc(mlBottom(sort), KLabel('#Or', sort), filter(lambda x: not is_bottom(x), disjuncts))


def mlImplies(antecedent: KInner, consequent: KInner, sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Implies', sort)(antecedent, consequent)


def mlExists(var: KVariable, body: KInner, sort: str | KSort = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Exists', sort)(var, body)


def mlCeil(  # noqa: N802
    term: KInner,
    arg_sort: str | KSort = GENERATED_TOP_CELL,
    sort: str | KSort = GENERATED_TOP_CELL,
) -> KApply:
    return KLabel('#Ceil', arg_sort, sort)(term)
