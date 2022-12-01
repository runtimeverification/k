from itertools import count
from typing import Dict, Final, List, Tuple

import pytest

from pyk.kast.inner import KApply, KInner, KLabel, KRewrite, KSequence, KSort, KVariable
from pyk.kast.manip import (
    bool_to_ml_pred,
    collapse_dots,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    simplify_bool,
    split_config_from,
    substitute,
)
from pyk.prelude.k import DOTS, GENERATED_TOP_CELL
from pyk.prelude.kbool import BOOL, FALSE, TRUE, andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlEqualsTrue, mlTop

from .utils import a, b, c, f, k, x

K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
GENERATED_TOP_CELL_2 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])

PUSH_REWRITES_TEST_DATA: Final = (
    (KRewrite(KSequence([f(a), b]), KSequence([f(c), b])), KSequence([f(KRewrite(a, c)), b])),
)


@pytest.mark.parametrize('term,expected', PUSH_REWRITES_TEST_DATA, ids=count())
def test_push_down_rewrites(term: KInner, expected: KInner) -> None:
    # When
    actual = push_down_rewrites(term)

    # Then
    assert actual == expected


STATE: Final = KLabel('<state>')
PC: Final = KLabel('<pc>')
MINIMIZE_TERM_TEST_DATA: Final[Tuple[Tuple[KInner, List[str], List[str], KInner], ...]] = (
    (f(k(a), STATE(a), PC(a)), [], [], f(k(a), STATE(a), PC(a))),
    (f(k(a), STATE(a), PC(a)), ['<k>'], [], f(STATE(a), PC(a), DOTS)),
    (f(k(a), STATE(a), PC(a)), [], ['<state>'], f(STATE(a), DOTS)),
)


@pytest.mark.parametrize('term,abstract_labels,keep_cells,expected', MINIMIZE_TERM_TEST_DATA, ids=count())
def test_minimize_term(term: KInner, abstract_labels: List[str], keep_cells: List[str], expected: KInner) -> None:
    # When
    actual = minimize_term(term, abstract_labels=abstract_labels, keep_cells=keep_cells)

    # Then
    assert actual == expected


# TODO: We'd like for bool_to_ml_pred and ml_pred_to_bool to be somewhat invertible.
ML_TO_BOOL_TEST_DATA: Final = (
    (
        'equals-true',
        False,
        KApply(KLabel('#Equals', [BOOL, GENERATED_TOP_CELL]), [TRUE, f(a)]),
        f(a),
    ),
    ('top-sort-bool', False, KApply(KLabel('#Top', [BOOL])), TRUE),
    ('top-no-sort', False, KApply('#Top'), TRUE),
    ('top-no-sort', False, mlTop(), TRUE),
    ('equals-variabl', False, KApply(KLabel('#Equals'), [x, f(a)]), KApply('_==K_', [x, f(a)])),
    ('equals-true-no-sort', False, KApply(KLabel('#Equals'), [TRUE, f(a)]), f(a)),
    (
        'equals-token',
        False,
        KApply(KLabel('#Equals', [KSort('Int'), GENERATED_TOP_CELL]), [intToken(3), f(a)]),
        KApply('_==K_', [intToken(3), f(a)]),
    ),
    ('not-top', False, KApply(KLabel('#Not', [GENERATED_TOP_CELL]), [mlTop()]), notBool(TRUE)),
    ('equals-term', True, KApply(KLabel('#Equals'), [f(a), f(x)]), KApply('_==K_', [f(a), f(x)])),
    (
        'simplify-and-true',
        False,
        KApply(KLabel('#And', [GENERATED_TOP_CELL]), [mlEqualsTrue(TRUE), mlEqualsTrue(TRUE)]),
        TRUE,
    ),
    (
        'ceil-set-concat-no-sort',
        True,
        KApply(
            KLabel('#Ceil', [KSort('Set'), GENERATED_TOP_CELL]),
            [KApply(KLabel('_Set_'), [KVariable('_'), KVariable('_')])],
        ),
        KVariable('Ceil_0f9c9997'),
    ),
    (
        'ceil-set-concat-sort',
        True,
        KApply(
            KLabel('#Not', [GENERATED_TOP_CELL]),
            [
                KApply(
                    KLabel('#Ceil', [KSort('Set'), GENERATED_TOP_CELL]),
                    [KApply(KLabel('_Set_'), [KVariable('_'), KVariable('_')])],
                )
            ],
        ),
        notBool(KVariable('Ceil_0f9c9997')),
    ),
    (
        'exists-equal-int',
        True,
        KApply(
            KLabel('#Exists', [INT, BOOL]),
            [KVariable('X'), KApply('_==Int_', [KVariable('X'), KVariable('Y')])],
        ),
        KVariable('Exists_6acf2557'),
    ),
)


@pytest.mark.parametrize(
    'test_id,unsafe,ml_pred,expected',
    ML_TO_BOOL_TEST_DATA,
    ids=[test_id for test_id, *_ in ML_TO_BOOL_TEST_DATA],
)
def test_ml_pred_to_bool(test_id: str, unsafe: bool, ml_pred: KInner, expected: KInner) -> None:
    # When
    actual = ml_pred_to_bool(ml_pred, unsafe=unsafe)

    # Then
    assert actual == expected


BOOL_TO_ML_TEST_DATA = (('equals-true', KApply(KLabel('#Equals', BOOL, GENERATED_TOP_CELL), TRUE, f(a)), f(a)),)


@pytest.mark.parametrize(
    'test_id,expected,term',
    BOOL_TO_ML_TEST_DATA,
    ids=[test_id for test_id, *_ in BOOL_TO_ML_TEST_DATA],
)
def test_bool_to_ml_pred(test_id: str, expected: KInner, term: KInner) -> None:
    # When
    actual = bool_to_ml_pred(term)

    # Then
    assert actual == expected


REMOVE_GENERATED_TEST_DATA = (
    (GENERATED_TOP_CELL_1, T_CELL),
    (GENERATED_TOP_CELL_2, T_CELL),
)


@pytest.mark.parametrize('term,expected', REMOVE_GENERATED_TEST_DATA, ids=count())
def test_remove_generated_cells(term: KInner, expected: KInner) -> None:
    # When
    actual = remove_generated_cells(term)

    # Then
    assert actual == expected


def test_collapse_dots() -> None:
    # Given
    term = substitute(GENERATED_TOP_CELL_1, {'MAP': DOTS, '_GENERATED_COUNTER_PLACEHOLDER': DOTS})
    expected = KApply('<generatedTop>', KApply('<T>', K_CELL, DOTS), DOTS)

    # When
    actual = collapse_dots(term)

    # Then
    assert actual == expected


SIMPLIFY_BOOL_TEST_DATA = (
    ('trivial-false', andBool([FALSE, TRUE]), FALSE),
    (
        'and-true',
        andBool([KApply('_==Int_', [intToken(3), intToken(4)]), TRUE]),
        KApply('_==Int_', [intToken(3), intToken(4)]),
    ),
    ('not-false', notBool(FALSE), TRUE),
)


@pytest.mark.parametrize(
    'test_id,term,expected',
    SIMPLIFY_BOOL_TEST_DATA,
    ids=[test_id for test_id, *_ in SIMPLIFY_BOOL_TEST_DATA],
)
def test_simplify_bool(test_id: str, term: KInner, expected: KInner) -> None:
    # When
    actual = simplify_bool(term)

    # Then
    assert actual == expected


MAP_ITEM_CELL = KApply('<mapItem>', KApply('foo'))
SPLIT_CONFIG_TEST_DATA = (
    (
        KApply('<k>', KSequence(KApply('foo'), KApply('bar'))),
        KApply('<k>', KVariable('K_CELL')),
        {'K_CELL': KSequence(KApply('foo'), KApply('bar'))},
    ),
    (
        KApply('<mapCell>', KApply('map_join', MAP_ITEM_CELL, MAP_ITEM_CELL)),
        KApply('<mapCell>', KVariable('MAPCELL_CELL')),
        {'MAPCELL_CELL': KApply('map_join', MAP_ITEM_CELL, MAP_ITEM_CELL)},
    ),
)


@pytest.mark.parametrize('term,expected_config,expected_subst', SPLIT_CONFIG_TEST_DATA, ids=count())
def test_split_config_from(term: KInner, expected_config: KInner, expected_subst: Dict[str, KInner]) -> None:
    # When
    actual_config, actual_subst = split_config_from(term)

    # Then
    assert actual_config == expected_config
    assert actual_subst == expected_subst
