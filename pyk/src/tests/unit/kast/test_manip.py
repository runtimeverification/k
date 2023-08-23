from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KLabel, KRewrite, KSequence, KSort, KToken, KVariable, Subst
from pyk.kast.manip import (
    bool_to_ml_pred,
    collapse_dots,
    is_term_like,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    rename_generated_vars,
    simplify_bool,
    split_config_from,
)
from pyk.prelude.k import DOTS, GENERATED_TOP_CELL
from pyk.prelude.kbool import BOOL, FALSE, TRUE, andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlEqualsTrue, mlTop

from ..utils import a, b, c, f, k, x

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner


K_CELL = KApply('<k>', [KSequence([KVariable('S1'), KVariable('_DotVar0')])])
T_CELL = KApply('<T>', [K_CELL, KApply('<state>', [KVariable('MAP')])])
GENERATED_COUNTER_CELL = KApply('<generatedCounter>', [KVariable('X')])
GENERATED_TOP_CELL_1 = KApply('<generatedTop>', [T_CELL, KVariable('_GENERATED_COUNTER_PLACEHOLDER')])
GENERATED_TOP_CELL_2 = KApply('<generatedTop>', [T_CELL, GENERATED_COUNTER_CELL])

PUSH_REWRITES_TEST_DATA: Final = (
    (KRewrite(KSequence([f(a), b]), KSequence([f(c), b])), KSequence([f(KRewrite(a, c)), b])),
    (KRewrite(KSequence([a, b]), KSequence([b])), KSequence([KRewrite(KSequence([a]), KSequence([])), b])),
    (KRewrite(KSequence([a, x]), x), KSequence([KRewrite(KSequence([a]), KSequence([])), x])),
)


@pytest.mark.parametrize('term,expected', PUSH_REWRITES_TEST_DATA, ids=count())
def test_push_down_rewrites(term: KInner, expected: KInner) -> None:
    # When
    actual = push_down_rewrites(term)

    # Then
    assert actual == expected


STATE: Final = KLabel('<state>')
PC: Final = KLabel('<pc>')
MINIMIZE_TERM_TEST_DATA: Final[tuple[tuple[KInner, list[str], list[str], KInner], ...]] = (
    (f(k(a), STATE(a), PC(a)), [], [], f(k(a), STATE(a), PC(a))),
    (f(k(a), STATE(a), PC(a)), ['<k>'], [], f(STATE(a), PC(a), DOTS)),
    (f(k(a), STATE(a), PC(a)), [], ['<state>'], f(STATE(a), DOTS)),
)


@pytest.mark.parametrize('term,abstract_labels,keep_cells,expected', MINIMIZE_TERM_TEST_DATA, ids=count())
def test_minimize_term(term: KInner, abstract_labels: list[str], keep_cells: list[str], expected: KInner) -> None:
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
    (
        'equals-true-comm',
        False,
        KApply(KLabel('#Equals', [BOOL, GENERATED_TOP_CELL]), [f(a), TRUE]),
        f(a),
    ),
    (
        'equals-false',
        False,
        KApply(KLabel('#Equals', [BOOL, GENERATED_TOP_CELL]), [FALSE, f(a)]),
        notBool(f(a)),
    ),
    (
        'equals-false-comm',
        False,
        KApply(KLabel('#Equals', [BOOL, GENERATED_TOP_CELL]), [f(a), FALSE]),
        notBool(f(a)),
    ),
    ('top-sort-bool', False, KApply(KLabel('#Top', [BOOL])), TRUE),
    ('top-no-sort', False, KApply('#Top'), TRUE),
    ('top-no-sort', False, mlTop(), TRUE),
    ('equals-variabl', False, KApply(KLabel('#Equals'), [x, f(a)]), KApply('_==K_', [x, f(a)])),
    ('equals-true-no-sort', False, KApply(KLabel('#Equals'), [TRUE, f(a)]), f(a)),
    ('equals-true-comm-no-sort', False, KApply(KLabel('#Equals'), [f(a), TRUE]), f(a)),
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
        KVariable('Ceil_fa9c0b54'),
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
        notBool(KVariable('Ceil_fa9c0b54')),
    ),
    (
        'exists-equal-int',
        True,
        KApply(
            KLabel('#Exists', [INT, BOOL]),
            [KVariable('X'), KApply('_==Int_', [KVariable('X'), KVariable('Y')])],
        ),
        KVariable('Exists_9a5d09ae'),
    ),
    (
        'kapply-equal-kappy',
        False,
        KApply(
            KLabel('#Equals', [KSort('Int'), KSort('GeneratedTopCell')]),
            (
                KApply(
                    KLabel('#lookup(_,_)_EVM-TYPES_Int_Map_Int', []),
                    (KVariable('?STORAGE', KSort('Map')), KToken('32', KSort('Int'))),
                ),
                KApply(
                    KLabel('#lookup(_,_)_EVM-TYPES_Int_Map_Int', []),
                    (KVariable('?STORAGE', KSort('Map')), KToken('32', KSort('Int'))),
                ),
            ),
        ),
        KApply(
            KLabel('_==K_', []),
            (
                KApply(
                    KLabel('#lookup(_,_)_EVM-TYPES_Int_Map_Int', []),
                    (KVariable('?STORAGE', KSort('Map')), KToken('32', KSort('Int'))),
                ),
                KApply(
                    KLabel('#lookup(_,_)_EVM-TYPES_Int_Map_Int', []),
                    (KVariable('?STORAGE', KSort('Map')), KToken('32', KSort('Int'))),
                ),
            ),
        ),
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


RENAME_GENERATED_VARS_TEST_DATA = (
    (
        'non-generated',
        KApply(
            '<k>',
            KSequence(
                KVariable('Gen'),
                KVariable('DotVar'),
                KVariable('?Gen'),
                KVariable('?DotVar'),
                KVariable('_notGen'),
                KVariable('_notDotVar'),
                KVariable('?_notGen'),
                KVariable('?_ntDotVar'),
            ),
        ),
        KApply(
            '<k>',
            KSequence(
                KVariable('Gen'),
                KVariable('DotVar'),
                KVariable('?Gen'),
                KVariable('?DotVar'),
                KVariable('_notGen'),
                KVariable('_notDotVar'),
                KVariable('?_notGen'),
                KVariable('?_ntDotVar'),
            ),
        ),
    ),
    (
        'name-conflicts',
        KApply('<k>', KSequence(KVariable('_Gen'), KVariable('_DotVar'), KVariable('?_Gen'), KVariable('?_DotVar'))),
        KApply(
            '<k>',
            KSequence(
                KVariable('K_CELL_8b13e996'),
                KVariable('K_CELL_3ee7a189'),
                KVariable('K_CELL_40796e18'),
                KVariable('K_CELL_20fb46a2'),
            ),
        ),
    ),
    (
        'nested-cells',
        KApply(
            '<k>', [KApply('<cell1>', KVariable('_Gen1')), KApply('<cell2>', KApply('<cell3>', KVariable('_Gen2')))]
        ),
        KApply(
            '<k>',
            [
                KApply('<cell1>', KVariable('CELL1_CELL_dbe3b121')),
                KApply('<cell2>', KApply('<cell3>', KVariable('CELL3_CELL_125dfae6'))),
            ],
        ),
    ),
    (
        'multiple-args',
        KApply(
            '<generatedTop>',
            [
                KApply('<k>', (KRewrite(lhs=KVariable('_Gen0'), rhs=KVariable('?_Gen1')))),
                KApply('<generatedCounter>', KVariable('GENERATEDCOUNTER_CELL')),
                KApply(
                    '<outerCell>',
                    KRewrite(lhs=KVariable('_Gen1'), rhs=KVariable('_Gen4')),
                    KRewrite(lhs=KVariable('_Gen3'), rhs=KVariable('_Gen5')),
                ),
            ],
        ),
        KApply(
            '<generatedTop>',
            [
                KApply('<k>', (KRewrite(lhs=KVariable('K_CELL_7d91010a'), rhs=KVariable('K_CELL_3efbf5b5')))),
                KApply('<generatedCounter>', KVariable('GENERATEDCOUNTER_CELL')),
                KApply(
                    '<outerCell>',
                    KRewrite(lhs=KVariable('OUTERCELL_CELL_dbe3b121'), rhs=KVariable('OUTERCELL_CELL_3efb5235')),
                    KRewrite(lhs=KVariable('OUTERCELL_CELL_82e8f7a8'), rhs=KVariable('OUTERCELL_CELL_f301f679')),
                ),
            ],
        ),
    ),
    (
        'no-outer-cell',
        KApply('#And', [KApply('<k>', KVariable('_Gen1')), KVariable('_Gen2')]),
        KApply('#And', [KApply('<k>', KVariable('K_CELL_dbe3b121')), KVariable('_Gen2')]),
    ),
)


@pytest.mark.parametrize(
    'test_id,term,expected',
    RENAME_GENERATED_VARS_TEST_DATA,
    ids=[test_id for test_id, *_ in RENAME_GENERATED_VARS_TEST_DATA],
)
def test_rename_generated_vars(test_id: str, term: KInner, expected: KInner) -> None:
    # When
    actual = rename_generated_vars(term)

    # Then
    assert actual == expected


def test_collapse_dots() -> None:
    # Given
    term = Subst({'MAP': DOTS, '_GENERATED_COUNTER_PLACEHOLDER': DOTS})(GENERATED_TOP_CELL_1)
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
def test_split_config_from(term: KInner, expected_config: KInner, expected_subst: dict[str, KInner]) -> None:
    # When
    actual_config, actual_subst = split_config_from(term)

    # Then
    assert actual_config == expected_config
    assert actual_subst == expected_subst


IS_TERM_LIKE_TEST_DATA = [
    ('var_with_at', KVariable('@S1'), False),
    ('var_without_at', KVariable('S1'), True),
    *[
        (f'label_{label_name}', KApply(KLabel(label_name), [KVariable('S1'), KVariable('S2')]), False)
        for label_name in ['#Equals', '#And', '#Or', '#Implies']
    ],
    ('label_lookup', KApply(KLabel('<kevm>')), True),
    ('nested-1', KApply(KLabel('<output>'), [KApply(KLabel('#And'), [KVariable('S1'), KVariable('S2')])]), False),
    ('nested-2', KApply(KLabel('<pc>'), [KApply(KLabel('#lookup'), [KVariable('S1'), KVariable('@S2')])]), False),
]


@pytest.mark.parametrize(
    'test_id,kast,expected',
    IS_TERM_LIKE_TEST_DATA,
    ids=[test_id for test_id, *_ in IS_TERM_LIKE_TEST_DATA],
)
def test_is_term_like(test_id: str, kast: KInner, expected: bool) -> None:
    assert is_term_like(kast) == expected
