from __future__ import annotations

from typing import TYPE_CHECKING

from ..kast.inner import KApply, KSort, KToken

if TYPE_CHECKING:
    from typing import Final

    from ..kast import KInner

INT: Final = KSort('Int')


def intToken(i: int) -> KToken:  # noqa: N802
    r"""Instantiate the KAST term ``#token(i, "Int")``.

    Args:
        i: The integer literal.

    Returns:
        The KAST term ``#token(i, "Int")``.
    """
    return KToken(str(i), INT)


def ltInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_<Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_<Int_`(i1, i2)``.
    """
    return KApply('_<Int_', i1, i2)


def leInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_<=Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_<=Int_`(i1, i2)``.
    """
    return KApply('_<=Int_', i1, i2)


def gtInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_>Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_>Int_`(i1, i2)``.
    """
    return KApply('_>Int_', i1, i2)


def geInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_>=Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_>=Int_`(i1, i2)``.
    """
    return KApply('_>=Int_', i1, i2)


def eqInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_==Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_==Int_`(i1, i2)``.
    """
    return KApply('_==Int_', i1, i2)


def neqInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_=/=Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_=/=Int_`(i1, i2)``.
    """
    return KApply('_=/=Int_', i1, i2)


def notInt(i: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```~Int_`(i)``.

    Args:
        i: The integer operand.

    Returns:
        The KAST term ```Int_`(i)``.
    """
    return KApply('~Int_', i)


def expInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_^Int_`(i1, i2)``.

    Args:
        i1: The base.
        i2: The exponent.

    Returns:
        The KAST term ```_^Int_`(i1, i2)``.
    """
    return KApply('_^Int_', i1, i2)


def expModInt(i1: KInner, i2: KInner, i3: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_^%Int__`(i1, i2, i3)``.

    Args:
        i1: The dividend.
        i2: The divisior.
        i3: The modulus.

    Returns:
        The KAST term ```_^%Int__`(i1, i2, i3)``.
    """
    return KApply('_^%Int__', i1, i2, i3)


def mulInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_*Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_*Int_`(i1, i2)``.
    """
    return KApply('_*Int_', i1, i2)


def divInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_/Int_`(i1, i2)``.

    Args:
        i1: The dividend.
        i2: The divisor.

    Returns:
        The KAST term ```_/Int_`(i1, i2)``.
    """
    return KApply('_/Int_', i1, i2)


def modInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_%Int_`(i1, i2)``.

    Args:
        i1: The dividend.
        i2: The divisor.

    Returns:
        The KAST term ```_%Int_`(i1, i2)``.
    """
    return KApply('_%Int_', i1, i2)


def euclidDivInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_divInt_`(i1, i2)``.

    Args:
        i1: The dividend.
        i2: The divisor.

    Returns:
        The KAST term ```_divInt_`(i1, i2)``.
    """
    return KApply('_divInt_', i1, i2)


def euclidModInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_modInt_`(i1, i2)``.

    Args:
        i1: The dividend.
        i2: The divisor.

    Returns:
        The KAST term ```_modInt_`(i1, i2)``.
    """
    return KApply('_modInt_', i1, i2)


def addInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_+Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_+Int_`(i1, i2)``.
    """
    return KApply('_+Int_', i1, i2)


def subInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_-Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_-Int_`(i1, i2)``.
    """
    return KApply('_-Int_', i1, i2)


def rshiftInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_>>Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_>>Int_`(i1, i2)``.
    """
    return KApply('_>>Int_', i1, i2)


def lshiftInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_<<Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_<<Int_`(i1, i2)``.
    """
    return KApply('_<<Int_', i1, i2)


def andInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_&Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_&Int_`(i1, i2)``.
    """
    return KApply('_&Int_', i1, i2)


def xorInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_xorInt_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_xorInt_`(i1, i2)``.
    """
    return KApply('_xorInt_', i1, i2)


def orInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```_|Int_`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```_|Int_`(i1, i2)``.
    """
    return KApply('_|Int_', i1, i2)


def minInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```minInt`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```minInt`(i1, i2)``.
    """
    return KApply('minInt', i1, i2)


def maxInt(i1: KInner, i2: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```maxInt`(i1, i2)``.

    Args:
        i1: The left operand.
        i2: The right operand.

    Returns:
        The KAST term ```maxInt`(i1, i2)``.
    """
    return KApply('maxInt', i1, i2)


def absInt(i: KInner) -> KApply:  # noqa: N802
    r"""Instantiate the KAST term ```absInt`(i)``.

    Args:
        i: The integer operand.

    Returns:
        The KAST term ```absInt`(i)``.
    """
    return KApply('absInt', i)
