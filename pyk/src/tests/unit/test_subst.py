from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KLabel, KVariable, Subst
from pyk.kast.manip import extract_subst
from pyk.prelude.kbool import TRUE
from pyk.prelude.kint import intToken
from pyk.prelude.ml import mlAnd, mlEquals, mlEqualsTrue, mlTop

from .utils import a, b, c, f, g, h, x, y, z

if TYPE_CHECKING:
    from typing import Dict, Final, Optional, Tuple

    from pyk.kast import KInner


COMPOSE_TEST_DATA: Tuple[Tuple[Dict[str, KInner], Dict[str, KInner], Dict[str, KInner]], ...] = (
    ({}, {}, {}),
    ({'x': x}, {}, {}),
    ({}, {'x': x}, {}),
    ({'x': y}, {}, {'x': y}),
    ({}, {'x': y}, {'x': y}),
    ({'y': x}, {'x': y}, {'y': x}),
    ({'x': z}, {'x': y}, {'x': y}),
    ({'y': z}, {'x': y}, {'x': z, 'y': z}),
    ({'x': y}, {'x': f(x)}, {'x': f(y)}),
    ({'x': f(x)}, {'x': f(x)}, {'x': f(f(x))}),
    ({'y': f(z)}, {'x': f(y)}, {'x': f(f(z)), 'y': f(z)}),
)


@pytest.mark.parametrize('subst1,subst2,expected', COMPOSE_TEST_DATA, ids=count())
def test_compose(subst1: Dict[str, KInner], subst2: Dict[str, KInner], expected: Dict[str, KInner]) -> None:
    # When
    actual = dict((Subst(subst1) * Subst(subst2)).minimize())

    # Then
    assert actual == expected


UNION_TEST_DATA: Tuple[Tuple[Dict[str, KInner], Dict[str, KInner], Optional[Dict[str, KInner]]], ...] = (
    ({}, {}, {}),
    ({'x': x}, {}, {'x': x}),
    ({}, {'x': x}, {'x': x}),
    ({'x': x, 'y': y}, {'x': x}, {'x': x, 'y': y}),
    ({'x': x, 'y': y}, {'z': z}, {'x': x, 'y': y, 'z': z}),
    ({'x': x}, {'x': y}, None),
    ({'x': x, 'y': y}, {'x': y}, None),
)


@pytest.mark.parametrize('subst1,subst2,expected', UNION_TEST_DATA, ids=count())
def test_union(
    subst1: Dict[str, KInner],
    subst2: Dict[str, KInner],
    expected: Optional[Dict[str, KInner]],
) -> None:
    # When
    actual_subst = Subst(subst1).union(Subst(subst2))
    actual = dict(actual_subst) if actual_subst is not None else None

    # Then
    assert actual == expected


APPLY_TEST_DATA: Tuple[Tuple[KInner, Dict[str, KInner], KInner], ...] = (
    (a, {}, a),
    (x, {}, x),
    (a, {'x': b}, a),
    (x, {'x': a}, a),
    (f(x), {'x': f(x)}, f(f(x))),
    (f(a, g(x, a)), {'x': b}, f(a, g(b, a))),
    (f(g(h(x, y, z))), {'x': a, 'y': b, 'z': c}, f(g(h(a, b, c)))),
)


@pytest.mark.parametrize('pattern,subst,expected', APPLY_TEST_DATA, ids=count())
def test_apply(pattern: KInner, subst: Dict[str, KInner], expected: KInner) -> None:
    # When
    actual = Subst(subst)(pattern)

    # Then
    assert actual == expected


UNAPPLY_TEST_DATA: Tuple[Tuple[KInner, Dict[str, KInner], KInner], ...] = (
    (a, {}, a),
    (a, {'x': a}, x),
    (y, {'x': y}, x),
    (f(a), {'x': f(a)}, x),
    (f(f(a)), {'x': f(a)}, f(x)),
    (f(x), {'x': f(a)}, f(x)),
    (f(x), {'x': f(x)}, x),
)


@pytest.mark.parametrize('term,subst,expected', UNAPPLY_TEST_DATA, ids=count())
def test_unapply(term: KInner, subst: Dict[str, KInner], expected: KInner) -> None:
    # When
    actual = Subst(subst).unapply(term)

    # Then
    assert actual == expected


ML_PRED_TEST_DATA: Final = (
    ('empty', Subst({}), KApply('#Top')),
    ('singleton', Subst({'X': TRUE}), KApply('#Equals', [KVariable('X'), TRUE])),
    (
        'double',
        Subst({'X': TRUE, 'Y': intToken(4)}),
        KApply(
            '#And',
            [KApply('#Equals', [KVariable('X'), TRUE]), KApply('#Equals', [KVariable('Y'), intToken(4)])],
        ),
    ),
)


@pytest.mark.parametrize('test_id,subst,pred', ML_PRED_TEST_DATA, ids=[test_id for test_id, *_ in ML_PRED_TEST_DATA])
def test_ml_pred(test_id: str, subst: Subst, pred: KInner) -> None:
    assert subst.ml_pred == pred


_0 = intToken(0)
_EQ = KLabel('_==Int_')
EXTRACT_SUBST_TEST_DATA: Final[Tuple[Tuple[KInner, Dict[str, KInner], KInner], ...]] = (
    (a, {}, a),
    (mlEquals(a, b), {}, mlEquals(a, b)),
    (mlEquals(x, a), {'x': a}, mlTop()),
    (mlEquals(x, _0), {}, mlEquals(x, _0)),
    (mlEquals(x, y), {}, mlEquals(x, y)),
    (mlAnd([mlEquals(a, b), mlEquals(x, a)]), {'x': a}, mlEquals(a, b)),
    (mlEqualsTrue(_EQ(a, b)), {}, mlEqualsTrue(_EQ(a, b))),
    (mlEqualsTrue(_EQ(x, a)), {'x': a}, mlTop()),
)


@pytest.mark.parametrize('term,expected_subst,expected_term', EXTRACT_SUBST_TEST_DATA, ids=count())
def test_extract_subst(term: KInner, expected_subst: Dict[str, KInner], expected_term: KInner) -> None:
    # When
    actual_subst, actual_term = extract_subst(term)

    # Then
    assert dict(actual_subst) == expected_subst
    assert actual_term == expected_term


def test_propagate_subst() -> None:
    # Given
    v1 = KVariable('V1')
    x = KVariable('X')
    bar_x = KApply('bar', [x])
    config = KApply('<k>', [bar_x])

    subst_conjunct = mlEquals(v1, bar_x)
    other_conjunct = mlEqualsTrue(KApply('_<=Int_', [v1, KApply('foo', [x, bar_x])]))

    term = mlAnd([config, subst_conjunct, other_conjunct])
    term_wo_subst = mlAnd([config, other_conjunct])

    # When
    subst, _ = extract_subst(term)
    actual = subst.unapply(term_wo_subst)

    # Then
    expected_config = KApply('<k>', [v1])
    expected_conjunct = mlEqualsTrue(KApply('_<=Int_', [v1, KApply('foo', [x, v1])]))
    expected = mlAnd([expected_config, expected_conjunct])

    assert actual == expected
