from typing import Final, Iterable

from ..kast import BOOL as KAST_BOOL
from ..kast import FALSE as KAST_FALSE
from ..kast import TRUE as KAST_TRUE
from ..kast import KApply, KInner, KLabel, KToken, build_assoc
from ..utils import unique

BOOL: Final = KAST_BOOL
TRUE: Final = KAST_TRUE
FALSE: Final = KAST_FALSE


def boolToken(b: bool) -> KToken:  # noqa: N802
    return TRUE if b else FALSE


def andBool(items: Iterable[KInner]) -> KInner:  # noqa: N802
    return build_assoc(TRUE, KLabel('_andBool_'), unique(items))


def orBool(items: Iterable[KInner]) -> KInner:  # noqa: N802
    return build_assoc(FALSE, KLabel('_orBool_'), unique(items))


def notBool(item: KInner) -> KApply:  # noqa: N802
    return KApply(KLabel('notBool_'), [item])


def impliesBool(antecedent: KInner, consequent: KInner) -> KApply:  # noqa: N802
    return KApply(KLabel('_impliesBool_'), [antecedent, consequent])
