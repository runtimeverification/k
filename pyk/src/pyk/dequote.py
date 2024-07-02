from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Final


def enquote_string(s: str) -> str:
    return ''.join(enquoted(s))


def dequote_string(s: str) -> str:
    return ''.join(dequoted(s))


def enquote_bytes(s: str) -> str:
    return ''.join(enquoted(s, allow_unicode=False))


def dequote_bytes(s: str) -> str:
    return ''.join(dequoted(s, allow_unicode=False))


def bytes_encode(s: str) -> bytes:
    return s.encode('latin-1')


def bytes_decode(b: bytes) -> str:
    return b.decode('latin-1')


NORMAL = 1
ESCAPE = 2
CPOINT = 3

ESCAPE_TABLE: Final = {
    '"': '"',
    '\\': '\\',
    'n': '\n',
    't': '\t',
    'r': '\r',
    'f': '\f',
}

CPOINT_TABLE: Final = {
    'x': 2,
    'u': 4,
    'U': 8,
}

HEX_TABLE = {c: int(c, 16) for c in '0123456789abcdefABCDEF'}


def dequoted(it: Iterable[str], *, allow_unicode: bool = True) -> Iterator[str]:
    acc = 0
    cnt = 0
    state = NORMAL
    for c in it:
        if state == CPOINT:
            if c not in HEX_TABLE:
                raise ValueError(f'Expected hex digit, got: {c}')

            acc *= 16
            acc += HEX_TABLE[c]
            cnt -= 1
            if cnt == 0:
                yield chr(acc)
                acc = 0
                state = NORMAL

        elif state == ESCAPE:
            if c in CPOINT_TABLE:
                if not allow_unicode and c != 'x':
                    raise ValueError(fr'Unicode escape sequence not allowed: \{c}')
                cnt = CPOINT_TABLE[c]
                state = CPOINT
            elif c in ESCAPE_TABLE:
                yield ESCAPE_TABLE[c]
                state = NORMAL
            else:
                raise ValueError(fr'Unexpected escape sequence: \{c}')

        elif c == '\\':
            state = ESCAPE

        else:
            yield c

    if state == CPOINT:
        raise ValueError('Incomplete Unicode code point')
    elif state == ESCAPE:
        raise ValueError('Incomplete escape sequence')


ENQUOTE_TABLE: Final = {
    ord('\t'): r'\t',  # 9
    ord('\n'): r'\n',  # 10
    ord('\f'): r'\f',  # 12
    ord('\r'): r'\r',  # 13
    ord('"'): r'\"',  # 34
    ord('\\'): r'\\',  # 92
}


def enquoted(it: Iterable[str], *, allow_unicode: bool = True) -> Iterator[str]:
    for c in it:
        code = ord(c)
        if code in ENQUOTE_TABLE:
            yield ENQUOTE_TABLE[code]
        elif 32 <= code < 127:
            yield c
        elif code <= 0xFF:
            yield fr'\x{code:02x}'
        elif not allow_unicode:
            raise ValueError(f"Unicode character not allowed: '{c}' ({code})")
        elif code <= 0xFFFF:
            yield fr'\u{code:04x}'
        elif code <= 0xFFFFFFFF:
            yield fr'\U{code:08x}'
        else:
            raise ValueError(f"Unsupported character: '{c}' ({code})")
