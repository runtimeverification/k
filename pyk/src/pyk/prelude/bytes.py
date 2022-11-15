from typing import Final

from ..kast.inner import KSort, KToken

BYTES: Final = KSort('Bytes')


def bytesToken(s: str) -> KToken:  # noqa: N802
    return KToken(f'b"{s}"', BYTES)
