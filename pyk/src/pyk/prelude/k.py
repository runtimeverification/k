from __future__ import annotations

from typing import TYPE_CHECKING

from ..kast.inner import KApply, KLabel, KSort, KToken

if TYPE_CHECKING:
    from typing import Final

    from ..kast import KInner


K: Final = KSort('K')
K_ITEM: Final = KSort('KItem')
GENERATED_TOP_CELL: Final = KSort('GeneratedTopCell')

DOTS: Final = KToken('...', K)


def inj(from_sort: KSort, to_sort: KSort, term: KInner) -> KInner:
    return KApply(KLabel('inj', (from_sort, to_sort)), (term,))
