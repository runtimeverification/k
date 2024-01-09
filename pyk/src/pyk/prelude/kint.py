from __future__ import annotations

from typing import TYPE_CHECKING

from ..kast.inner import KApply, KSort, KToken

if TYPE_CHECKING:
    from typing import Final

    from ..kast import KInner

INT: Final = KSort('Int')


def intToken(i: int) -> KToken:  # noqa: N802
    return KToken(str(i), INT)


def ltInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_<Int_', i1, i2)


def leInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_<=Int_', i1, i2)


def gtInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_>Int_', i1, i2)


def geInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_>=Int_', i1, i2)


def eqInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_==Int_', i1, i2)
