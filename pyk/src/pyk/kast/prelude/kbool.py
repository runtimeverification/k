from __future__ import annotations

from typing import TYPE_CHECKING

from ...utils import unique
from ..inner import KApply, KLabel, KSort, KToken, build_assoc

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from .. import KInner

BOOL: Final = KSort('Bool')
TRUE: Final = KToken('true', BOOL)
FALSE: Final = KToken('false', BOOL)


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
