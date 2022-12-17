from itertools import count
from typing import Collection, Dict, Iterable, List

import pytest

from pyk.kore.manip import free_occs
from pyk.kore.syntax import And, EVar, Exists, Pattern, SortApp, Top

S = SortApp('S')
x, y = (EVar(name, S) for name in ('x', 'y'))

FREE_OCCS_TEST_DATA: Iterable = (
    (Top(S), [], {}),
    (x, [], {'x': [x]}),
    (x, ['x'], {}),
    (And(S, x, y), [], {'x': [x], 'y': [y]}),
    (And(S, x, x), [], {'x': [x, x]}),
    (And(S, x, y), ['x'], {'y': [y]}),
    (And(S, x, x), ['x'], {}),
    (Exists(S, x, x), [], {}),
    (Exists(S, x, y), [], {'y': [y]}),
    (And(S, x, Exists(S, y, y)), [], {'x': [x]}),
)


@pytest.mark.parametrize('pattern,bound_vars,expected', FREE_OCCS_TEST_DATA, ids=count())
def test_free_occs(pattern: Pattern, bound_vars: Collection[str], expected: Dict[str, List[EVar]]) -> None:
    # When
    actual = free_occs(pattern, bound_vars=bound_vars)

    # Then
    assert actual == expected
