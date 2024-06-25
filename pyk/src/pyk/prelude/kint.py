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


def neqInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_=/=Int_', i1, i2)


def notInt(i1: KInner) -> KApply:  # noqa: N802
    return KApply('~Int_', i1)


def expInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_^Int_', i1, i2)


def expModInt(i1: KInner, i2: KInner, i3: KInner) -> KApply:  # noqa: N802
    return KApply('_^%Int__', i1, i2, i3)


def mulInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_*Int_', i1, i2)


def divInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_/Int_', i1, i2)


def modInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_%Int_', i1, i2)


def euclidDivInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_divInt_', i1, i2)


def euclidModInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_modInt_', i1, i2)


def addInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_+Int_', i1, i2)


def subInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_-Int_', i1, i2)


def rshiftInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_>>Int_', i1, i2)


def lshiftInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_<<Int_', i1, i2)


def andInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_&Int_', i1, i2)


def xorInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_xorInt_', i1, i2)


def orInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('_|Int_', i1, i2)


def minInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('minInt(_,_)_INT-COMMON_Int_Int_Int', i1, i2)


def maxInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    return KApply('maxInt(_,_)_INT-COMMON_Int_Int_Int', i1, i2)


def absInt(i1: KInner) -> KApply:  # noqa: N802
    return KApply('absInt(_)_INT-COMMON_Int_Int', i1)
