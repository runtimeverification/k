from typing import Final

from ..dequote import bytes_decode, bytes_encode, dequote_bytes, enquote_bytes
from ..kast.inner import KSort, KToken

BYTES: Final = KSort('Bytes')


def bytesToken_from_str(pretty: str) -> KToken:  # noqa: N802
    return KToken(f'b"{enquote_bytes(pretty)}"', BYTES)


def bytesToken(b: bytes) -> KToken:  # noqa: N802
    return bytesToken_from_str(bytes_decode(b))


def pretty_bytes_str(token: KToken) -> str:
    if token.sort != BYTES:
        raise ValueError(f'Expected Bytes token, got: {token}')
    assert token.token[0:2] == 'b"'
    assert token.token[-1] == '"'
    return dequote_bytes(token.token[2:-1])


def pretty_bytes(token: KToken) -> bytes:
    return bytes_encode(pretty_bytes_str(token))
