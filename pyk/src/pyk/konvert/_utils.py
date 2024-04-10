from __future__ import annotations

from typing import TYPE_CHECKING

from ..utils import FrozenDict

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Final


UNMUNGE_TABLE: Final[FrozenDict[str, str]] = FrozenDict(
    {
        'Spce': ' ',
        'Bang': '!',
        'Quot': '"',
        'Hash': '#',
        'Dolr': '$',
        'Perc': '%',
        'And-': '&',
        'Apos': "'",
        'LPar': '(',
        'RPar': ')',
        'Star': '*',
        'Plus': '+',
        'Comm': ',',
        'Stop': '.',
        'Slsh': '/',
        'Coln': ':',
        'SCln': ';',
        '-LT-': '<',
        'Eqls': '=',
        '-GT-': '>',
        'Ques': '?',
        '-AT-': '@',
        'LSqB': '[',
        'RSqB': ']',
        'Bash': '\\',
        'Xor-': '^',
        'Unds': '_',
        'BQuo': '`',
        'LBra': '{',
        'Pipe': '|',
        'RBra': '}',
        'Tild': '~',
    }
)


MUNGE_TABLE: Final[FrozenDict[str, str]] = FrozenDict({v: k for k, v in UNMUNGE_TABLE.items()})


def munge(label: str) -> str:
    symbol = ''
    quot = False
    for c in label:
        if c in MUNGE_TABLE:
            symbol += "'" if not quot else ''
            symbol += MUNGE_TABLE[c]
            quot = True
        else:
            symbol += "'" if quot else ''
            symbol += c
            quot = False
    symbol += "'" if quot else ''
    return symbol


def unmunge(symbol: str) -> str:
    return ''.join(unmunged(symbol))


def unmunged(it: Iterable[str]) -> Iterator[str]:
    it = iter(it)

    startquote = False
    quote = False
    endquote = False
    buff: list[str] = []
    cnt = 0  # len(buff)

    for c in it:
        if c == "'":
            if startquote:
                raise ValueError('Empty quoted section')
            elif quote:
                if cnt == 0:
                    quote = False
                    endquote = True
                else:
                    fragment = ''.join(buff)
                    raise ValueError(f'Unexpected end of symbol: {fragment}')
            elif endquote:
                raise ValueError('Quoted sections next to each other')
            else:
                quote = True
                startquote = True

        else:
            startquote = False
            endquote = False
            if quote:
                if cnt == 3:
                    buff.append(c)
                    munged = ''.join(buff)
                    buff = []
                    cnt = 0
                    if not munged in UNMUNGE_TABLE:
                        raise ValueError(f'Unknown encoding "{munged}"')
                    yield UNMUNGE_TABLE[munged]
                else:
                    buff += [c]
                    cnt += 1
            else:
                yield c

    if quote:
        raise ValueError('Unterminated quoted section')
