from typing import Final

from ..kast import KApply, KSort, KToken

K: Final = KSort('K')
GENERATED_TOP_CELL: Final = KSort('GeneratedTopCell')

DOTS: Final = KToken('...', K)

EMPTY_K: Final = KApply('#EmptyK')
