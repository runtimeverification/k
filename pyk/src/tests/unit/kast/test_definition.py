from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

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
# ---------------------------------------------------------------------------

INT: Final = KSort('Int')
N: Final = KSort('N')
S1: Final = KSort('S1')
S2: Final = KSort('S2')
MINT_N: Final = KSort('MInt', (N,))
MINT_INT: Final = KSort('MInt', (INT,))
SORT_PARAM: Final = KSort('#SortParam')

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

DEFN: Final = KDefinition(
    'TEST',
    [KFlatModule('TEST', [_BAR_PROD, _FOO_PROD, _EQUALS_PROD])],
)


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
