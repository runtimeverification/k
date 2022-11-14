from typing import Iterable, Union

from ..kast.inner import KApply, KInner, KLabel, KSort, build_assoc
from .k import GENERATED_TOP_CELL
from .kbool import BOOL, TRUE


def is_top(term: KInner) -> bool:
    return isinstance(term, KApply) and term.label.name == '#Top'


def is_bottom(term: KInner) -> bool:
    return isinstance(term, KApply) and term.label.name == '#Bottom'


# TODO default sort K can be tightened using basic type inference
def mlEquals(  # noqa: N802
    term1: KInner,
    term2: KInner,
    arg_sort: Union[str, KSort] = GENERATED_TOP_CELL,
    sort: Union[str, KSort] = GENERATED_TOP_CELL,
) -> KApply:
    return KLabel('#Equals', arg_sort, sort)(term1, term2)


def mlEqualsTrue(term: KInner) -> KApply:  # noqa: N802
    return mlEquals(TRUE, term, BOOL)


def mlTop(sort: Union[str, KSort] = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Top', sort)()


def mlBottom(sort: Union[str, KSort] = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Bottom', sort)()


def mlNot(term: KInner, sort: Union[str, KSort] = GENERATED_TOP_CELL) -> KApply:  # noqa: N802
    return KLabel('#Not', sort)(term)


def mlAnd(conjuncts: Iterable[KInner], sort: Union[str, KSort] = GENERATED_TOP_CELL) -> KInner:  # noqa: N802
    return build_assoc(mlTop(sort), KLabel('#And', sort), conjuncts)


def mlOr(disjuncts: Iterable[KInner], sort: Union[str, KSort] = GENERATED_TOP_CELL) -> KInner:  # noqa: N802
    return build_assoc(mlBottom(sort), KLabel('#Or', sort), disjuncts)


def mlImplies(  # noqa: N802
    antecedent: KInner, consequent: KInner, sort: Union[str, KSort] = GENERATED_TOP_CELL
) -> KApply:
    return KLabel('#Implies', sort)(antecedent, consequent)
