from typing import Final, Iterable, Optional, Union, final

from .kast import FALSE, TRUE, KApply, KInner, KLabel, KSort, KToken
from .utils import unique


@final
class Sorts:
    BOOL: Final = KSort('Bool')
    INT: Final = KSort('Int')
    STRING: Final = KSort('String')
    K: Final = KSort('K')
    GENERATED_TOP_CELL: Final = KSort('GeneratedTopCell')

    def __init__(self):
        raise ValueError('Class Sorts should not be instantiated')


@final
class Labels:
    K_CELLS: Final = KLabel('#KCells')
    EMPTY_K: Final = KLabel('#EmptyK')

    def __init__(self):
        raise ValueError('Class Labels should not be instantiated')


@final
class Bool:

    true: Final = TRUE
    false: Final = FALSE

    def __init__(self):
        raise ValueError('Class Bool should not be instantiated')

    @staticmethod
    def of(b: bool) -> KToken:
        return Bool.true if b else Bool.false

    @staticmethod
    def andBool(items: Iterable[KInner]) -> KInner:  # noqa: N802
        return build_assoc(Bool.true, KLabel('_andBool_'), unique(items))

    @staticmethod
    def orBool(items: Iterable[KInner]) -> KInner:  # noqa: N802
        return build_assoc(Bool.false, KLabel('_orBool_'), unique(items))

    @staticmethod
    def notBool(item: KInner) -> KApply:  # noqa: N802
        return KApply(KLabel('notBool_'), [item])

    @staticmethod
    def impliesBool(antecedent: KInner, consequent: KInner) -> KApply:  # noqa: N802
        return KApply(KLabel('_impliesBool_'), [antecedent, consequent])


def build_assoc(unit: KInner, label: Union[str, KLabel], terms: Iterable[KInner]) -> KInner:
    _label = label if type(label) is KLabel else KLabel(label)
    res: Optional[KInner] = None
    for term in reversed(list(terms)):
        if term == unit:
            continue
        if not res:
            res = term
        else:
            res = _label(term, res)
    return res or unit


def build_cons(unit: KInner, label: Union[str, KLabel], terms: Iterable[KInner]) -> KInner:
    it = iter(terms)
    try:
        fst = next(it)
        return KApply(label, (fst, build_cons(unit, label, it)))
    except StopIteration:
        return unit


def token(x: Union[bool, int, str]) -> KToken:
    if type(x) is bool:
        return Bool.of(x)
    if type(x) is int:
        return intToken(x)
    if type(x) is str:
        return stringToken(x)
    raise AssertionError()


def intToken(i: int) -> KToken:  # noqa: N802
    return KToken(str(i), Sorts.INT)


def stringToken(s: str) -> KToken:  # noqa: N802
    return KToken(f'"{s}"', Sorts.STRING)


def ltInt(i1, i2):  # noqa: N802
    return KApply('_<Int_', i1, i2)


def leInt(i1, i2):  # noqa: N802
    return KApply('_<=Int_', i1, i2)


# TODO default sort K can be tightened using basic type inference
def mlEquals(  # noqa: N802
    term1: KInner,
    term2: KInner,
    arg_sort: Union[str, KSort] = Sorts.K,
    sort: Union[str, KSort] = Sorts.K,
) -> KApply:
    return KLabel('#Equals', arg_sort, sort)(term1, term2)


def mlEqualsTrue(term: KInner) -> KApply:  # noqa: N802
    return mlEquals(Bool.true, term, Sorts.BOOL)


def mlTop(sort: Union[str, KSort] = Sorts.K) -> KApply:  # noqa: N802
    return KLabel('#Top', sort)()


def mlBottom(sort: Union[str, KSort] = Sorts.K) -> KApply:  # noqa: N802
    return KLabel('#Top', sort)()


def mlNot(term: KInner, sort: Union[str, KSort] = Sorts.K) -> KApply:  # noqa: N802
    return KLabel('#Not', sort)(term)


def mlAnd(conjuncts: Iterable[KInner], sort: Union[str, KSort] = Sorts.K) -> KInner:  # noqa: N802
    return build_assoc(mlTop(sort), KLabel('#And', sort), conjuncts)


def mlOr(disjuncts: Iterable[KInner], sort: Union[str, KSort] = Sorts.K) -> KInner:  # noqa: N802
    return build_assoc(mlBottom(sort), KLabel('#Or', sort), disjuncts)


def mlImplies(antecedent: KInner, consequent: KInner, sort: Union[str, KSort] = Sorts.K) -> KApply:  # noqa: N802
    return KLabel('#Implies', sort)(antecedent, consequent)
