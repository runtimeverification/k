from typing import Final, Iterable, Union, final

from .kast import TRUE, KApply, KInner, KLabel, KSort, KToken


@final
class Sorts:
    BOOL: Final = KSort('Bool')
    INT: Final = KSort('Int')
    STRING: Final = KSort('String')
    K: Final = KSort('K')
    GENERATED_TOP_CELL: Final = KSort('GeneratedTopCell')

    def __init__(self):
        raise ValueError('Class Sorts should not be instantiated')


def buildAssoc(unit: KInner, label: Union[str, KLabel], ls: Iterable[KInner]) -> KInner:
    """Build an associative binary operator term given the join and unit ops.

    -   Input: unit, label, and list of elements to join.
    -   Output: cons-list style construction of the joined term.
    """
    ls = list(filter(lambda l: l != unit, ls))
    if len(ls) == 0:
        return unit
    if len(ls) == 1:
        return ls[0]
    if ls[0] == unit:
        return buildAssoc(unit, label, ls[1:])
    return KApply(label, [ls[0], buildAssoc(unit, label, ls[1:])])


def buildCons(unit, cons, ls):
    """Build a cons operator term given the cons and unit ops.

    -   Input: unit, cons, and list of elements to join.
    -   Output: cons-list style construction of the joined term.
    """
    if len(ls) == 0:
        return unit
    return KApply(cons, [ls[0], buildCons(unit, cons, ls[1:])])


def token(x: Union[bool, int, str]) -> KToken:
    if type(x) is bool:
        return boolToken(x)
    if type(x) is int:
        return intToken(x)
    if type(x) is str:
        return stringToken(x)
    assert False


def boolToken(b: bool) -> KToken:
    return KToken('true' if b else 'false', Sorts.BOOL)


def intToken(i: int) -> KToken:
    return KToken(str(i), Sorts.INT)


def stringToken(s: str) -> KToken:
    return KToken(f'"{s}"', Sorts.STRING)


def ltInt(i1, i2):
    return KApply('_<Int_', [i1, i2])


def leInt(i1, i2):
    return KApply('_<=Int_', [i1, i2])


# TODO default sort K can be tightened using basic type inference
def mlEquals(term1: KInner, term2: KInner, sort1: Union[str, KSort] = Sorts.K, sort2: Union[str, KSort] = Sorts.K) -> KApply:
    return KApply(KLabel('#Equals', (sort1, sort2)), (term1, term2))


def mlEqualsTrue(term: KInner) -> KApply:
    return mlEquals(TRUE, term, Sorts.BOOL)


def mlTop(sort: Union[str, KSort] = Sorts.K) -> KApply:
    return KApply(KLabel('#Top', (sort,)))


def mlBottom(sort: Union[str, KSort] = Sorts.K) -> KApply:
    return KApply(KLabel('#Top', (sort,)))


def mlNot(term: KInner, sort: Union[str, KSort] = Sorts.K) -> KApply:
    return KApply(KLabel('#Not', (sort,)), (term,))


def mlAnd(conjuncts: Iterable[KInner], sort: Union[str, KSort] = Sorts.K) -> KInner:
    return buildAssoc(mlTop(sort), KLabel('#And', (sort,)), conjuncts)


def mlOr(disjuncts: Iterable[KInner], sort: Union[str, KSort] = Sorts.K) -> KInner:
    return buildAssoc(mlBottom(sort), KLabel('#Or', (sort,)), disjuncts)


def mlImplies(antecedent: KInner, consequent: KInner, sort: Union[str, KSort] = Sorts.K) -> KApply:
    return KApply(KLabel('#Implies', (sort,)), (antecedent, consequent))
