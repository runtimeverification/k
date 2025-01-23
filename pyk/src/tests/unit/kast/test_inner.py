from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KVariable, flatten_label, keep_vars_sorted

from ..utils import a, f, g, x, y, z

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner

FLATTEN_LABEL_DATA: Final[tuple[tuple[str, KInner, list[KInner]], ...]] = (
    ('a', a, []),
    ('b', a, [a]),
    ('x', x, [x]),
    ('y', x, [x]),
    ('f', f(x), [x]),
    ('g', f(x), [f(x)]),
    ('f', f(x, y), [x, y]),
    ('f', f(x, x), [x, x]),
    ('f', f(x, y, z), [x, y, z]),
    ('f', f(f(x)), [x]),
    ('f', f(f(f(x))), [x]),
    ('f', f(g(f(x))), [g(f(x))]),
    ('f', f(f(x, y, z)), [x, y, z]),
    ('f', f(x, f(y, x, f(y)), z), [x, y, x, y, z]),
    ('f', f(x, f(y, x, f(g(f(y))), z)), [x, y, x, g(f(y)), z]),
)


@pytest.mark.parametrize('label,kast,expected', FLATTEN_LABEL_DATA, ids=count())
def test_flatten_label(label: str, kast: KInner, expected: list[KInner]) -> None:
    # When
    actual = flatten_label(label, kast)

    # Then
    assert actual == expected


KEEP_VARS_SORTED_DATA: Final[tuple[tuple[dict[str, list[KVariable]], dict[str, KVariable]], ...]] = (
    (
        {'a': [KVariable('a'), KVariable('a')], 'b': [KVariable('b'), KVariable('b')]},
        {'a': KVariable('a'), 'b': KVariable('b')},
    ),
    (
        {'a': [KVariable('a', 'K'), KVariable('a', 'X')], 'b': [KVariable('b', 'K'), KVariable('b', 'X')]},
        {'a': KVariable('a'), 'b': KVariable('b')},
    ),
    (
        {'a': [KVariable('a', 'K'), KVariable('a')], 'b': [KVariable('b', 'K'), KVariable('b', 'K')]},
        {'a': KVariable('a', 'K'), 'b': KVariable('b', 'K')},
    ),
    (
        {'a': [KVariable('a', 'A'), KVariable('a'), KVariable('a', 'B')]},
        {'a': KVariable('a')},
    ),
)


@pytest.mark.parametrize('occurrences,expected', KEEP_VARS_SORTED_DATA, ids=count())
def test_keep_vars_sorted(occurrences: dict[str, list[KVariable]], expected: dict[str, KVariable]) -> None:
    # When
    actual = keep_vars_sorted(occurrences)

    # Then
    assert actual == expected
