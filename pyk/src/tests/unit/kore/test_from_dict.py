from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.syntax import And, App, Or, Pattern, SortVar

if TYPE_CHECKING:
    from collections.abc import Mapping
    from typing import Any, Final


symbols = ['a', 'b', 'c', 'd']
a, b, c, d = (App(symbol) for symbol in symbols)
ad, bd, cd, dd = ({'tag': 'App', 'name': name, 'sorts': [], 'args': []} for name in symbols)

S = SortVar('S')
Sd = {'tag': 'SortVar', 'name': 'S'}

TEST_DATA: Final = (
    (
        'nullary-and',
        {'tag': 'And', 'sort': Sd, 'patterns': []},
        And(S, ()),
    ),
    (
        'unary-and',
        {'tag': 'And', 'sort': Sd, 'patterns': [ad]},
        And(S, (a,)),
    ),
    (
        'binary-and',
        {'tag': 'And', 'sort': Sd, 'patterns': [ad, bd]},
        And(S, (a, b)),
    ),
    (
        'ternary-and',
        {'tag': 'And', 'sort': Sd, 'patterns': [ad, bd, cd]},
        And(S, (a, b, c)),
    ),
    (
        'quaternary-and',
        {'tag': 'And', 'sort': Sd, 'patterns': [ad, bd, cd, dd]},
        And(S, (a, b, c, d)),
    ),
    (
        'nullary-or',
        {'tag': 'Or', 'sort': Sd, 'patterns': []},
        Or(S, ()),
    ),
    (
        'unary-or',
        {'tag': 'Or', 'sort': Sd, 'patterns': [ad]},
        Or(S, (a,)),
    ),
    (
        'binary-or',
        {'tag': 'Or', 'sort': Sd, 'patterns': [ad, bd]},
        Or(S, (a, b)),
    ),
    (
        'ternary-or',
        {'tag': 'Or', 'sort': Sd, 'patterns': [ad, bd, cd]},
        Or(S, (a, b, c)),
    ),
    (
        'quaternary-or',
        {'tag': 'Or', 'sort': Sd, 'patterns': [ad, bd, cd, dd]},
        Or(S, (a, b, c, d)),
    ),
)


@pytest.mark.parametrize('test_id,dct,expected', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
def test_from_dict(test_id: str, dct: Mapping[str, Any], expected: Pattern) -> None:
    # When
    actual = Pattern.from_dict(dct)

    # Then
    assert actual == expected
