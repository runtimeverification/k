from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import flatten_label

from ..utils import a, f, g, x, y, z

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner

MATCH_TEST_DATA: Final[tuple[tuple[str, KInner, list[KInner]], ...]] = (
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


@pytest.mark.parametrize('label,kast,flist', MATCH_TEST_DATA, ids=count())
def test_flatten_label(label: str, kast: KInner, flist: list[KInner]) -> None:
    # When
    flattened = flatten_label(label, kast)
    print(flattened)

    # Then
    assert flattened is not None
    assert flattened == flist
