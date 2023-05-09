from typing import Final

from ..dequote import dequote_string, enquote_string
from ..kast.inner import KSort, KToken

STRING: Final = KSort('String')


def stringToken(pretty: str) -> KToken:  # noqa: N802
    return KToken(f'"{enquote_string(pretty)}"', STRING)


def pretty_string(token: KToken) -> str:
    if token.sort != STRING:
        raise ValueError(f'Expected String token, got: {token}')
    assert token.token[0] == '"' == token.token[-1]
    return dequote_string(token.token[1:-1])
