from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KSequence
from pyk.kast.prelude.ml import mlBottom, mlTop

from ..utils import a, b, c, f, g, h, x, y, z

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner


MATCH_TEST_DATA: Final[tuple[tuple[KInner, KInner], ...]] = (
    (a, a),
    (a, x),
    (f(a), x),
    (f(a), f(a)),
    (f(a), f(x)),
    (f(a, b), f(x, y)),
    (f(a, b, c), f(x, y, z)),
    (f(g(h(a))), f(x)),
    (f(g(h(x))), f(x)),
    (f(a, g(b, h(c))), f(x, y)),
    (KSequence([a, x]), KSequence([y])),
    (KSequence([a, b, x]), KSequence([a, y])),
    (KSequence([f(a), b, x]), KSequence([f(z), y])),
    (KSequence([f(a), b, c, x]), KSequence([f(z), y])),
)


@pytest.mark.parametrize('term,pattern', MATCH_TEST_DATA, ids=count())
def test_match_and_subst(term: KInner, pattern: KInner) -> None:
    # When
    subst = pattern.match(term)

    # Then
    assert subst is not None
    assert subst(pattern) == term


NO_MATCH_TEST_DATA: Final[tuple[tuple[KInner, KInner], ...]] = (
    (f(x, x), f(x, a)),
    (mlTop(), mlBottom()),
    (KSequence([a, b, c]), KSequence([x, x])),
)


@pytest.mark.parametrize('term,pattern', NO_MATCH_TEST_DATA, ids=count())
def test_no_match(term: KInner, pattern: KInner) -> None:
    # When
    subst = pattern.match(term)

    # Then
    assert subst is None
