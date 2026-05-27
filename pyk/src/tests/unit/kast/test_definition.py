from __future__ import annotations

import logging
from typing import TYPE_CHECKING

import pytest

from pyk.kast.att import Atts, KAtt
from pyk.kast.inner import KApply, KAs, KLabel, KSequence, KSort, KToken, KVariable
from pyk.kast.outer import (
    KDefinition,
    KFlatModule,
    KNonTerminal,
    KProduction,
    KTerminal,
    _match_sort_params,
    _sort_contains,
)

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Final

    from pyk.kast.inner import KInner


# ---------------------------------------------------------------------------
# Minimal test definition
#
# bar:    syntax N       ::= bar(N)           -- result sort is the param directly
# foo:    syntax MInt{N} ::= foo(MInt{N})     -- result/arg sorts nest the param
# baz:    syntax MInt{N} ::= baz()            -- no args; param bound only from expected sort
# #Equals: syntax S2     ::= #Equals{S1,S2}(S1, S1)  -- ML pred, result sort context-dependent
#
# Subsort: syntax Int ::= MInt{Int}  -- MInt{Int} <: Int (enables subsort-aware matching)
#
# Cell map fragment:
#   AccountCellMap ::= AccountCellMap AccountCellMap  [cellCollection, element(AccountCellMapItem), wrapElement(<account>)]
#   AccountCellMap ::= AccountCellMapItem(Int, AccountCell)
#   AccountCell    ::= <account>(Int, Int)
#   AccountCell    ::= getEntry(AccountCell)           -- takes element sort, NOT map sort
# ---------------------------------------------------------------------------

INT: Final = KSort('Int')
N: Final = KSort('N')
S1: Final = KSort('S1')
S2: Final = KSort('S2')
S3: Final = KSort('S3')
MINT_N: Final = KSort('MInt', (N,))
MINT_INT: Final = KSort('MInt', (INT,))
SORT_PARAM: Final = KSort('#SortParam')
ACCOUNT_CELL_MAP: Final = KSort('AccountCellMap')
ACCOUNT_CELL: Final = KSort('AccountCell')

_BAR_PROD: Final = KProduction(
    sort=N,
    items=[KTerminal('bar'), KTerminal('('), KNonTerminal(N), KTerminal(')')],
    params=[N],
    klabel='bar',
)

_FOO_PROD: Final = KProduction(
    sort=MINT_N,
    items=[KTerminal('foo'), KTerminal('('), KNonTerminal(MINT_N), KTerminal(')')],
    params=[N],
    klabel='foo',
)

_EQUALS_PROD: Final = KProduction(
    sort=S2,
    items=[KNonTerminal(S1), KNonTerminal(S1)],
    params=[S1, S2],
    klabel='#Equals',
)

# Hypothetical 3-param #Equals to test the multi-unbound-param guard.
# S1 is inferred from arguments; S2 and S3 are both unbound, which the single-sentinel
# scheme cannot handle — add_sort_params must raise NotImplementedError.
_EQUALS3_PROD: Final = KProduction(
    sort=S2,
    items=[KNonTerminal(S1), KNonTerminal(S1)],
    params=[S1, S2, S3],
    klabel='#Equals',
)

# User-defined label where S2 does not appear in any argument sort, so it remains
# unbound after argument processing.  add_sort_params must emit a warning and
# return the term unchanged (best-effort).
_PAIR_PROD: Final = KProduction(
    sort=KSort('Pair', (S1, S2)),
    items=[KTerminal('pair'), KTerminal('('), KNonTerminal(S1), KTerminal(')')],
    params=[S1, S2],
    klabel='pair',
)

# syntax MInt{N} ::= baz()  — no argument sorts; param N only bound via expected_sort
_BAZ_PROD: Final = KProduction(
    sort=MINT_N,
    items=[KTerminal('baz'), KTerminal('('), KTerminal(')')],
    params=[N],
    klabel='baz',
)

# syntax Int ::= MInt{Int}  — subsort declaration: MInt{Int} <: Int
# Enables the subsort-aware matching path (Java AddSortInjections.match step 3).
_MINT_INT_SUBSORT: Final = KProduction(sort=INT, items=[KNonTerminal(MINT_INT)])

_ACCT_MAP_CONCAT: Final = KProduction(
    sort=ACCOUNT_CELL_MAP,
    items=[KNonTerminal(ACCOUNT_CELL_MAP), KNonTerminal(ACCOUNT_CELL_MAP)],
    klabel='_AccountCellMap_',
    att=KAtt(entries=[Atts.CELL_COLLECTION(None), Atts.ELEMENT('AccountCellMapItem'), Atts.WRAP_ELEMENT('<account>')]),
)

_ACCT_MAP_ITEM: Final = KProduction(
    sort=ACCOUNT_CELL_MAP,
    items=[
        KTerminal('AccountCellMapItem'),
        KTerminal('('),
        KNonTerminal(INT),
        KTerminal(','),
        KNonTerminal(ACCOUNT_CELL),
        KTerminal(')'),
    ],
    klabel='AccountCellMapItem',
)

_ACCOUNT_CELL: Final = KProduction(
    sort=ACCOUNT_CELL,
    items=[
        KTerminal('<account>'),
        KTerminal('('),
        KNonTerminal(INT),
        KTerminal(','),
        KNonTerminal(INT),
        KTerminal(')'),
    ],
    klabel='<account>',
)

_GET_ENTRY: Final = KProduction(
    sort=ACCOUNT_CELL,
    items=[KTerminal('getEntry'), KTerminal('('), KNonTerminal(ACCOUNT_CELL), KTerminal(')')],
    klabel='getEntry',
)

DEFN: Final = KDefinition(
    'TEST',
    [
        KFlatModule(
            'TEST',
            [
                _BAR_PROD,
                _FOO_PROD,
                _BAZ_PROD,
                _EQUALS_PROD,
                _MINT_INT_SUBSORT,
                _ACCT_MAP_CONCAT,
                _ACCT_MAP_ITEM,
                _ACCOUNT_CELL,
                _GET_ENTRY,
            ],
        )
    ],
)

# Definition used only to verify the multi-unbound-param guard in add_sort_params.
DEFN3: Final = KDefinition('TEST3', [KFlatModule('TEST3', [_EQUALS3_PROD])])

# Definition used only to verify the unresolvable-user-label warning path.
DEFN_PAIR: Final = KDefinition('TEST_PAIR', [KFlatModule('TEST_PAIR', [_PAIR_PROD])])


# ---------------------------------------------------------------------------
# KDefinition.sort
# ---------------------------------------------------------------------------

SORT_DATA: Final = (
    # Basic leaf terms
    ('ktoken', KToken('42', INT), INT),
    ('kvariable_with_sort', KVariable('X', sort=INT), INT),
    ('ksequence', KSequence([]), KSort('K')),
    # KApply: result sort substituted directly from param
    ('kapply_direct_result', KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)]), INT),
    # KApply: result sort nests the param (MInt{N} with N→Int → MInt{Int})
    ('kapply_nested_result', KApply(KLabel('foo', [INT]), [KVariable('X', sort=MINT_INT)]), MINT_INT),
    # KApply with unfilled sort params: sort() returns None rather than raising
    ('kapply_unfilled_params', KApply(KLabel('foo'), [KVariable('X', sort=MINT_INT)]), None),
    # KApply with unknown label: KeyError from symbols lookup → None
    ('kapply_unknown_label', KApply(KLabel('nonexistent'), []), None),
    # KAs: sort of the alias variable
    ('kas_sorted_alias', KAs(KVariable('X', sort=MINT_INT), KVariable('Y', sort=MINT_INT)), MINT_INT),
    # KAs whose alias has no sort annotation: returns None
    ('kas_unsorted_alias', KAs(KVariable('X', sort=MINT_INT), KVariable('Y')), None),
)


@pytest.mark.parametrize(
    'test_id,term,expected',
    SORT_DATA,
    ids=[test_id for test_id, *_ in SORT_DATA],
)
def test_sort(test_id: str, term: KInner, expected: KSort | None) -> None:
    assert DEFN.sort(term) == expected


# ---------------------------------------------------------------------------
# KDefinition.resolve_sorts
# ---------------------------------------------------------------------------

RESOLVE_SORTS_DATA: Final = (
    # Direct substitution: result sort IS the param (N → Int)
    ('direct_bar', KLabel('bar', [INT]), INT, (INT,)),
    # Recursive substitution: result/arg sort nests the param (MInt{N} with N → Int → MInt{Int})
    ('nested_foo', KLabel('foo', [INT]), MINT_INT, (MINT_INT,)),
)


@pytest.mark.parametrize(
    'test_id,label,expected_result,expected_args',
    RESOLVE_SORTS_DATA,
    ids=[test_id for test_id, *_ in RESOLVE_SORTS_DATA],
)
def test_resolve_sorts(test_id: str, label: KLabel, expected_result: KSort, expected_args: tuple[KSort, ...]) -> None:
    result, args = DEFN.resolve_sorts(label)
    assert result == expected_result
    assert args == expected_args


# ---------------------------------------------------------------------------
# KDefinition.add_sort_params
# ---------------------------------------------------------------------------

ADD_SORT_PARAMS_DATA: Final = (
    # Label already has params filled: leave unchanged
    (
        'already_filled',
        KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)]),
        KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)]),
    ),
    # Direct sort param: psort IS the param (N ~ Int → N=Int)
    (
        'direct_param',
        KApply(KLabel('bar'), [KVariable('X', sort=INT)]),
        KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)]),
    ),
    # Nested sort param: psort = MInt{N}, asort = MInt{Int} → N=Int via unification
    (
        'nested_param',
        KApply(KLabel('foo'), [KVariable('X', sort=MINT_INT)]),
        KApply(KLabel('foo', [INT]), [KVariable('X', sort=MINT_INT)]),
    ),
    # ML pred: S1 inferred from args, S2 (result sort) filled with #SortParam sentinel
    (
        'ml_pred_sentinel',
        KApply('#Equals', [KVariable('X', sort=INT), KVariable('Y', sort=INT)]),
        KApply(KLabel('#Equals', [INT, SORT_PARAM]), [KVariable('X', sort=INT), KVariable('Y', sort=INT)]),
    ),
    # Unsortable argument (no sort annotation): cannot fill params, term returned unchanged
    (
        'unsortable_arg_unchanged',
        KApply(KLabel('foo'), [KVariable('X')]),
        KApply(KLabel('foo'), [KVariable('X')]),
    ),
    # Subsort-aware: arg sort is Int, but MInt{Int} <: Int in DEFN, so N=Int via subsort match
    # (this case would fail with structural-only unification since Int ≠ MInt{N}).
    # Note: X keeps sort Int even though the resolved production argument sort is MInt{Int}.
    # add_sort_params only fills KLabel sort params; it does not check or modify variable sorts.
    (
        'subsort_aware',
        KApply(KLabel('foo'), [KVariable('X', sort=INT)]),
        KApply(KLabel('foo', [INT]), [KVariable('X', sort=INT)]),
    ),
)


@pytest.mark.parametrize(
    'test_id,term,expected',
    ADD_SORT_PARAMS_DATA,
    ids=[test_id for test_id, *_ in ADD_SORT_PARAMS_DATA],
)
def test_add_sort_params(test_id: str, term: KInner, expected: KInner) -> None:
    assert DEFN.add_sort_params(term) == expected


def test_add_sort_params_multi_unbound_raises() -> None:
    # #Equals with 3 sort params: S1 is inferred from arguments, S2 and S3 are both unbound.
    # The single-sentinel scheme cannot distinguish them, so NotImplementedError must be raised.
    term = KApply('#Equals', [KVariable('X', sort=INT), KVariable('Y', sort=INT)])
    with pytest.raises(NotImplementedError, match='2 unbound sort parameters'):
        DEFN3.add_sort_params(term)


def test_add_sort_params_user_label_unresolvable_warns(caplog: pytest.LogCaptureFixture) -> None:
    # pair(S1, S2) has S2 absent from arguments — S2 is unbound after inference.
    # add_sort_params emits a warning and returns the term unchanged (best-effort).
    term = KApply(KLabel('pair'), [KVariable('X', sort=INT)])
    with caplog.at_level(logging.WARNING):
        result = DEFN_PAIR.add_sort_params(term)
    assert result == term
    assert any('could not infer sort params' in record.message for record in caplog.records)


# ---------------------------------------------------------------------------
# KDefinition.infer_sort_params
# ---------------------------------------------------------------------------
#
# Tests the public method directly (not through add_sort_params), mirroring the
# Java AddSortInjections.substituteProd() test scenarios derived from the algorithm.

INFER_SORT_PARAMS_DATA: Final[
    tuple[
        tuple[str, KProduction, tuple[KSort | None, ...], KSort | None, dict[KSort, KSort | None], KSort | None],
        ...,
    ]
] = (
    # Direct param: psort IS the param (N → Int); prod.sort=N → inferred=Int
    ('direct_param', _BAR_PROD, (INT,), None, {N: INT}, INT),
    # Nested param: psort = MInt{N}, asort = MInt{Int} → N=Int; prod.sort=MInt{N} → inferred=MInt{Int}
    ('nested_param', _FOO_PROD, (MINT_INT,), None, {N: INT}, MINT_INT),
    # Subsort-aware: arg sort is Int, MInt{Int} <: Int in DEFN → N=Int via subsort iteration
    ('subsort_aware', _FOO_PROD, (INT,), None, {N: INT}, MINT_INT),
    # matchExpected: baz() has no arg sorts; N bound from expected_sort MInt{Int} → inferred=MInt{Int}
    ('expected_sort', _BAZ_PROD, (), MINT_INT, {N: INT}, MINT_INT),
    # None arg skipped; N has no candidates → inferred=None (parametric prod, N unbound)
    ('unbound_absent', _BAR_PROD, (None,), None, {}, None),
    # Conflicting args: S1→[Int,Bool] LUB fails → S1:None; S2 no candidates; prod.sort=S2 → inferred=None
    ('conflicting_args', _EQUALS_PROD, (INT, KSort('Bool')), None, {S1: None}, None),
    # expected_sort head mismatch: MInt{N} vs Int → no structural match → N absent → inferred=None
    ('expected_sort_mismatch', _BAZ_PROD, (), INT, {}, None),
    # Non-parametric: no params to bind, result sort is always concrete → inferred=AccountCell ≠ None
    # This distinguishes "trivially complete (no params)" from "params exist but no candidates".
    ('no_params_trivial', _ACCOUNT_CELL, (INT, INT), None, {}, ACCOUNT_CELL),
)


@pytest.mark.parametrize(
    'test_id,prod,actual_sorts,expected_sort,expected_bindings,expected_inferred_sort',
    INFER_SORT_PARAMS_DATA,
    ids=[test_id for test_id, *_ in INFER_SORT_PARAMS_DATA],
)
def test_infer_sort_params(
    test_id: str,
    prod: KProduction,
    actual_sorts: tuple[KSort | None, ...],
    expected_sort: KSort | None,
    expected_bindings: dict[KSort, KSort | None],
    expected_inferred_sort: KSort | None,
) -> None:
    bindings, inferred_sort = DEFN.infer_sort_params(prod, actual_sorts, expected_sort)
    assert bindings == expected_bindings
    assert inferred_sort == expected_inferred_sort


# ---------------------------------------------------------------------------
# _match_sort_params (module-level helper)
# ---------------------------------------------------------------------------
#
# Directly tests the three matching strategies described in the docstring.


MATCH_SORT_PARAMS_DATA: Final[
    tuple[
        tuple[
            str, KSort, KSort, frozenset[KSort], Callable[[KSort], frozenset[KSort]] | None, dict[KSort, list[KSort]]
        ],
        ...,
    ]
] = (
    # Case 1 – direct: parametric IS a sort param
    ('direct', N, INT, frozenset({N}), None, {N: [INT]}),
    # Case 2 – structural: same head, recurse on sub-params
    ('structural', MINT_N, MINT_INT, frozenset({N}), None, {N: [INT]}),
    # Case 2 fails (different heads), no subsorts_fn → empty
    ('structural_no_match_no_subsorts', MINT_N, INT, frozenset({N}), None, {}),
    # Case 3 – subsort-aware: MInt{N} vs Int; DEFN.subsorts yields MInt{Int} → N=Int
    ('subsort_aware', MINT_N, INT, frozenset({N}), DEFN.subsorts, {N: [INT]}),
    # No match in any case
    ('no_match', INT, KSort('Bool'), frozenset({N}), None, {}),
)


@pytest.mark.parametrize(
    'test_id,parametric,actual,params,subsorts_fn,expected',
    MATCH_SORT_PARAMS_DATA,
    ids=[test_id for test_id, *_ in MATCH_SORT_PARAMS_DATA],
)
def test_match_sort_params(
    test_id: str,
    parametric: KSort,
    actual: KSort,
    params: frozenset[KSort],
    subsorts_fn: Callable[[KSort], frozenset[KSort]] | None,
    expected: dict[KSort, list[KSort]],
) -> None:
    assert _match_sort_params(parametric, actual, params, subsorts_fn) == expected


# ---------------------------------------------------------------------------
# _sort_contains (module-level helper)
# ---------------------------------------------------------------------------

SORT_CONTAINS_DATA: Final = (
    ('param_itself', N, N, True),
    ('nested_one_level', MINT_N, N, True),
    ('nested_two_levels', KSort('Foo', (MINT_N,)), N, True),
    ('concrete_not_param', MINT_INT, N, False),
    ('unrelated', INT, N, False),
)


@pytest.mark.parametrize(
    'test_id,sort,param,expected',
    SORT_CONTAINS_DATA,
    ids=[test_id for test_id, *_ in SORT_CONTAINS_DATA],
)
def test_sort_contains(test_id: str, sort: KSort, param: KSort, expected: bool) -> None:
    assert _sort_contains(sort, param) == expected


# ---------------------------------------------------------------------------
# KDefinition.add_cell_map_items
# ---------------------------------------------------------------------------

_ACCT_1: Final = KApply('<account>', [KVariable('X', sort=INT), KVariable('Y', sort=INT)])
_ACCT_2: Final = KApply('<account>', [KVariable('A', sort=INT), KVariable('B', sort=INT)])

ADD_CELL_MAP_ITEMS_DATA: Final = (
    # Parent expects AccountCellMap (the map sort) — children are wrapped in AccountCellMapItem.
    (
        'wraps_when_parent_expects_cell_map_sort',
        KApply('_AccountCellMap_', [_ACCT_1, _ACCT_2]),
        KApply(
            '_AccountCellMap_',
            [
                KApply('AccountCellMapItem', [KVariable('X', sort=INT), _ACCT_1]),
                KApply('AccountCellMapItem', [KVariable('A', sort=INT), _ACCT_2]),
            ],
        ),
    ),
    # Parent expects AccountCell (the element sort) — the <account> child must NOT be wrapped.
    # Before the guard fix, _wrap_elements would incorrectly wrap here too.
    (
        'no_wrap_when_parent_expects_cell_element_sort',
        KApply('getEntry', [_ACCT_1]),
        KApply('getEntry', [_ACCT_1]),
    ),
)


@pytest.mark.parametrize(
    'test_id,term,expected',
    ADD_CELL_MAP_ITEMS_DATA,
    ids=[test_id for test_id, *_ in ADD_CELL_MAP_ITEMS_DATA],
)
def test_add_cell_map_items(test_id: str, term: KInner, expected: KInner) -> None:
    assert DEFN.add_cell_map_items(term) == expected
