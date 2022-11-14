from typing import Final

from ..kast.inner import KSort, KToken

STRING: Final = KSort('String')


def stringToken(s: str) -> KToken:  # noqa: N802
    return KToken(f'"{s}"', STRING)
