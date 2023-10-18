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
x, y, z = (EVar(name, s) for name in ('x', 'y', 'z'))
val = String('val')
app = App('app', (), (x, y))

ML_PATTERN_OF_TEST_DATA: Final = (
    ('top', r'\top', (s,), (), Top(s)),
    ('bottom', r'\bottom', (s,), (), Bottom(s)),
    ('not', r'\not', (s,), (x,), Not(s, x)),
    ('and0', r'\and', (s,), (), And(s, ())),
    ('and1', r'\and', (s,), (x,), And(s, (x,))),
    ('and2', r'\and', (s,), (x, y), And(s, (x, y))),
    ('and3', r'\and', (s,), (x, y, z), And(s, (x, y, z))),
    ('or0', r'\or', (s,), (), Or(s, ())),
    ('or1', r'\or', (s,), (x,), Or(s, (x,))),
    ('or2', r'\or', (s,), (x, y), Or(s, (x, y))),
    ('or3', r'\or', (s,), (x, y, z), Or(s, (x, y, z))),
    ('implies', r'\implies', (s,), (x, y), Implies(s, x, y)),
    ('iff', r'\iff', (s,), (x, y), Iff(s, x, y)),
    ('exists', r'\exists', (s,), (x, y), Exists(s, x, y)),
    ('forall', r'\forall', (s,), (x, y), Forall(s, x, y)),
    ('mu', r'\mu', (), (u, x), Mu(u, x)),
    ('nu', r'\nu', (), (u, x), Nu(u, x)),
    ('ceil', r'\ceil', (s, t), (x,), Ceil(s, t, x)),
    ('floor', r'\floor', (s, t), (x,), Floor(s, t, x)),
    ('equals', r'\equals', (s, t), (x, y), Equals(s, t, x, y)),
    ('in', r'\in', (s, t), (x, y), In(s, t, x, y)),
    ('next', r'\next', (s,), (x,), Next(s, x)),
    ('rewrites', r'\rewrites', (s,), (x, y), Rewrites(s, x, y)),
    ('dv', r'\dv', (s,), (val,), DV(s, val)),
    ('left-assoc', r'\left-assoc', (), (app,), LeftAssoc(app)),
    ('right-assoc', r'\right-assoc', (), (app,), RightAssoc(app)),
)


@pytest.mark.parametrize(
    'test_id,symbol,sorts,patterns,expected',
    ML_PATTERN_OF_TEST_DATA,
    ids=[test_id for test_id, *_ in ML_PATTERN_OF_TEST_DATA],
)
def test_ml_pattern_of(
    test_id: str,
    symbol: str,
    sorts: Iterable[Sort],
    patterns: Iterable[Pattern],
    expected: MLPattern,
) -> None:
    # When
    actual = MLPattern.of(symbol, sorts, patterns)

    # Then
    assert actual == expected
    assert actual.symbol() == symbol
    assert actual.sorts == sorts
    assert actual.ctor_patterns == patterns
