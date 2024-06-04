from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pykframework.kast.manip import count_vars

from ..utils import a, b, c, f, g, h, x, y, z

if TYPE_CHECKING:
    from collections.abc import Mapping
    from typing import Final

    from pykframework.kast import KInner


TEST_DATA: Final[tuple[tuple[KInner, Mapping[str, int]], ...]] = (
    (a, {}),
    (x, {'x': 1}),
    (f(a), {}),
    (f(a, b, c), {}),
    (f(x), {'x': 1}),
    (f(f(f(x))), {'x': 1}),
    (f(x, a), {'x': 1}),
    (f(x, x), {'x': 2}),
    (f(x, y), {'x': 1, 'y': 1}),
    (f(x, y, z), {'x': 1, 'y': 1, 'z': 1}),
    (f(x, g(y), h(z)), {'x': 1, 'y': 1, 'z': 1}),
    (f(x, a, g(y, b), h(z, c)), {'x': 1, 'y': 1, 'z': 1}),
    (f(x, g(x, y), h(x, z)), {'x': 3, 'y': 1, 'z': 1}),
    (f(x, g(x, h(x, y, z))), {'x': 3, 'y': 1, 'z': 1}),
)


@pytest.mark.parametrize('term,expected', TEST_DATA, ids=count())
def test(term: KInner, expected: Mapping) -> None:
    # When
    actual = count_vars(term)

    # Then
    assert actual == expected
