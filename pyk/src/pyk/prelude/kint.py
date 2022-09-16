from typing import Final

from ..kast import KApply, KSort, KToken

INT: Final = KSort('Int')


def intToken(i: int) -> KToken:  # noqa: N802
    return KToken(str(i), INT)


def ltInt(i1, i2):  # noqa: N802
    return KApply('_<Int_', i1, i2)


def leInt(i1, i2):  # noqa: N802
    return KApply('_<=Int_', i1, i2)
