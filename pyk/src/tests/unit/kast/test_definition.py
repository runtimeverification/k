from __future__ import annotations

import logging
from typing import TYPE_CHECKING

import pytest

from pyk.kast.att import Atts, KAtt
from pyk.kast.inner import KApply, KAs, KLabel, KSequence, KSort, KToken, KVariable
from pyk.kast.outer import KDefinition, KFlatModule, KNonTerminal, KProduction, KTerminal

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast.inner import KInner


# ---------------------------------------------------------------------------
# Minimal test definition
#
# bar: syntax N       ::= bar(N)        -- result sort is the param directly
# foo: syntax MInt{N} ::= foo(MInt{N})  -- result/arg sorts nest the param
# #Equals: syntax S2  ::= #Equals{S1,S2}(S1, S1)  -- ML pred, result sort context-dependent
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
            'TEST', [_BAR_PROD, _FOO_PROD, _EQUALS_PROD, _ACCT_MAP_CONCAT, _ACCT_MAP_ITEM, _ACCOUNT_CELL, _GET_ENTRY]
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
