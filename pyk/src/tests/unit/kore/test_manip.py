from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kore import manip
from pyk.kore.prelude import dv
from pyk.kore.syntax import And, EVar, Exists, SortApp, Top

if TYPE_CHECKING:
    from collections.abc import Collection, Iterable
    from typing import Final

    from pyk.kore.syntax import Pattern

S = SortApp('S')
x, y = (EVar(name, S) for name in ('x', 'y'))
a, b, c = (dv(val) for val in ['a', 'b', 'c'])


CONJUNCTS_TEST_DATA: Final = (
    (Top(S), ()),
    (a, (a,)),
    (And(S, (a,)), (a,)),
    (And(S, (a, b)), (a, b)),
    (And(S, (a, b, c)), (a, b, c)),
    (And(S, (a, b, Top(S))), (a, b)),
    (And(S, (And(S, (a, b)), c)), (a, b, c)),
    (And(S, (a, And(S, (b, c)))), (a, b, c)),
)


@pytest.mark.parametrize('pattern,expected', CONJUNCTS_TEST_DATA, ids=count())
def test_conjuncts(pattern: Pattern, expected: tuple[Pattern, ...]) -> None:
    # When
    actual = manip.conjuncts(pattern)

    # Then
    assert actual == expected


FREE_OCCS_TEST_DATA: Iterable = (
    (Top(S), [], {}),
    (x, [], {'x': [x]}),
    (x, ['x'], {}),
    (And(S, (x, y)), [], {'x': [x], 'y': [y]}),
    (And(S, (x, x)), [], {'x': [x, x]}),
    (And(S, (x, y)), ['x'], {'y': [y]}),
    (And(S, (x, x)), ['x'], {}),
    (Exists(S, x, x), [], {}),
    (Exists(S, x, y), [], {'y': [y]}),
    (And(S, (x, Exists(S, y, y))), [], {'x': [x]}),
)


@pytest.mark.parametrize('pattern,bound_vars,expected', FREE_OCCS_TEST_DATA, ids=count())
def test_free_occs(pattern: Pattern, bound_vars: Collection[str], expected: dict[str, list[EVar]]) -> None:
    # When
    actual = manip.free_occs(pattern, bound_vars=bound_vars)

    # Then
    assert actual == expected
