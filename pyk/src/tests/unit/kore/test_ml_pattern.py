from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.syntax import (
    DV,
    And,
    App,
    Bottom,
    Ceil,
    Equals,
    EVar,
    Exists,
    Floor,
    Forall,
    Iff,
    Implies,
    In,
    LeftAssoc,
    MLPattern,
    Mu,
    Next,
    Not,
    Nu,
    Or,
    Rewrites,
    RightAssoc,
    SortApp,
    String,
    SVar,
    Top,
)

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.kore.syntax import Pattern, Sort


s, t = (SortApp(name) for name in ('s', 't'))
u = SVar('@u', s)
x, y = (EVar(name, s) for name in ('x', 'y'))
val = String('val')
app = App('app', (), (x, y))

ML_PATTERN_OF_TEST_DATA: Final = (
    (r'\top', (s,), (), Top(s)),
    (r'\bottom', (s,), (), Bottom(s)),
    (r'\not', (s,), (x,), Not(s, x)),
    (r'\and', (s,), (x, y), And(s, x, y)),
    (r'\or', (s,), (x, y), Or(s, x, y)),
    (r'\implies', (s,), (x, y), Implies(s, x, y)),
    (r'\iff', (s,), (x, y), Iff(s, x, y)),
    (r'\exists', (s,), (x, y), Exists(s, x, y)),
    (r'\forall', (s,), (x, y), Forall(s, x, y)),
    (r'\mu', (), (u, x), Mu(u, x)),
    (r'\nu', (), (u, x), Nu(u, x)),
    (r'\ceil', (s, t), (x,), Ceil(s, t, x)),
    (r'\floor', (s, t), (x,), Floor(s, t, x)),
    (r'\equals', (s, t), (x, y), Equals(s, t, x, y)),
    (r'\in', (s, t), (x, y), In(s, t, x, y)),
    (r'\next', (s,), (x,), Next(s, x)),
    (r'\rewrites', (s,), (x, y), Rewrites(s, x, y)),
    (r'\dv', (s,), (val,), DV(s, val)),
    (r'\left-assoc', (), (app,), LeftAssoc('app', (), (x, y))),
    (r'\right-assoc', (), (app,), RightAssoc('app', (), (x, y))),
)


@pytest.mark.parametrize(
    'symbol,sorts,patterns,expected',
    ML_PATTERN_OF_TEST_DATA,
    ids=[symbol for symbol, *_ in ML_PATTERN_OF_TEST_DATA],
)
def test_ml_pattern_of(symbol: str, sorts: Iterable[Sort], patterns: Iterable[Pattern], expected: MLPattern) -> None:
    # When
    actual = MLPattern.of(symbol, sorts, patterns)

    # Then
    assert actual == expected
    assert actual.symbol() == symbol
    assert actual.sorts == sorts
    assert actual.ctor_patterns == patterns
