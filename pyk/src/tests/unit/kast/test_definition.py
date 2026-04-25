from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KAs, KLabel, KSort, KVariable
from pyk.kast.outer import KDefinition, KFlatModule, KNonTerminal, KProduction, KTerminal

if TYPE_CHECKING:
    from typing import Final


# ---------------------------------------------------------------------------
# Minimal test definition
#
# bar: syntax N    ::= bar(N)        [function]  -- result sort is the param directly
# foo: syntax MInt{N} ::= foo(MInt{N}) [function]  -- result/arg sorts nest the param
# #Equals: syntax S2 ::= #Equals{S1,S2}(S1, S1)   -- ML pred with context-dependent result sort
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
# KDefinition.sort — adjacent tests (pass at HEAD)
# ---------------------------------------------------------------------------


def test_sort_kvariable() -> None:
    """sort() returns the explicit sort annotation on a KVariable."""
    assert DEFN.sort(KVariable('X', sort=INT)) == INT


def test_sort_kapply_direct_result() -> None:
    """sort() for an application whose result sort is the param directly (bar{Int})."""
    term = KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)])
    assert DEFN.sort(term) == INT


# ---------------------------------------------------------------------------
# KDefinition.resolve_sorts — adjacent tests (pass at HEAD)
# ---------------------------------------------------------------------------


def test_resolve_sorts_direct() -> None:
    """resolve_sorts handles direct param substitution N → Int."""
    result_sort, arg_sorts = DEFN.resolve_sorts(KLabel('bar', [INT]))
    assert result_sort == INT
    assert arg_sorts == (INT,)


# ---------------------------------------------------------------------------
# KDefinition.add_sort_params — adjacent tests (pass at HEAD)
# ---------------------------------------------------------------------------


def test_add_sort_params_already_filled() -> None:
    """add_sort_params leaves a label alone when its params are already filled."""
    term = KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)])
    assert DEFN.add_sort_params(term) == term


def test_add_sort_params_direct_param() -> None:
    """add_sort_params fills a direct sort param by inspecting the argument sort."""
    term = KApply(KLabel('bar'), [KVariable('X', sort=INT)])
    expected = KApply(KLabel('bar', [INT]), [KVariable('X', sort=INT)])
    assert DEFN.add_sort_params(term) == expected


# ---------------------------------------------------------------------------
# KDefinition.sort — new-feature tests (fail at HEAD before the fix)
# ---------------------------------------------------------------------------


def test_sort_kapply_unfilled_params_returns_none() -> None:
    """sort() returns None (not raises) when the KApply label has unfilled sort params."""
    # When label has no params but the production requires them, old code raises ValueError
    # from resolve_sorts(); new code catches it and returns None instead.
    term = KApply(KLabel('foo'), [KVariable('X', sort=MINT_INT)])
    assert DEFN.sort(term) is None


def test_sort_kapply_nested_result_sort() -> None:
    """sort() resolves a result sort that nests the sort param (MInt{N} → MInt{Int})."""
    # Old code: resolve_sorts returns MInt{N} because sorts.get(MInt{N}, MInt{N}) leaves
    # the nested param unsubstituted.  New code recurses into the param tuple.
    term = KApply(KLabel('foo', [INT]), [KVariable('X', sort=MINT_INT)])
    assert DEFN.sort(term) == MINT_INT


def test_sort_kas() -> None:
    """sort() returns the sort of the alias variable in a KAs pattern."""
    # Old code has no KAs case and falls through to case _: return None.
    alias = KVariable('Y', sort=MINT_INT)
    term = KAs(pattern=KVariable('X', sort=MINT_INT), alias=alias)
    assert DEFN.sort(term) == MINT_INT


# ---------------------------------------------------------------------------
# KDefinition.resolve_sorts — new-feature tests (fail at HEAD before the fix)
# ---------------------------------------------------------------------------


def test_resolve_sorts_nested() -> None:
    """resolve_sorts recursively substitutes params nested inside compound sorts."""
    # foo has param N, result sort MInt{N}, arg sort MInt{N}.
    # With N → Int, both should resolve to MInt{Int}.
    # Old code: sorts.get(MInt{N}, MInt{N}) → MInt{N} unchanged (N is the key, not MInt{N}).
    result_sort, arg_sorts = DEFN.resolve_sorts(KLabel('foo', [INT]))
    assert result_sort == MINT_INT
    assert arg_sorts == (MINT_INT,)


# ---------------------------------------------------------------------------
# KDefinition.add_sort_params — new-feature tests (fail at HEAD before the fix)
# ---------------------------------------------------------------------------


def test_add_sort_params_nested_param() -> None:
    """add_sort_params fills a param that appears nested inside the argument sort."""
    # foo has param N and arg sort MInt{N}.  Given arg KVariable('X', sort=MInt{Int}),
    # the unifier extracts N → Int from the match MInt{N} ~ MInt{Int}.
    # Old code only handled the case psort IS the param (direct); it left nested cases unfilled.
    term = KApply(KLabel('foo'), [KVariable('X', sort=MINT_INT)])
    expected = KApply(KLabel('foo', [INT]), [KVariable('X', sort=MINT_INT)])
    assert DEFN.add_sort_params(term) == expected


def test_add_sort_params_ml_pred_sentinel() -> None:
    """add_sort_params fills the context-dependent result sort of an ML predicate with a sentinel."""
    # #Equals has params [S1, S2] where S2 is the axiom result sort (context-dependent).
    # Given args of sort Int, S1 → Int is inferable but S2 is not — so S2 gets the
    # sentinel KSort('#SortParam') so that krule_to_kore can introduce sort variable Q0.
    # Old code: no ML pred special case, returns the term unchanged (no params filled).
    term = KApply('#Equals', [KVariable('X', sort=INT), KVariable('Y', sort=INT)])
    expected = KApply(KLabel('#Equals', [INT, SORT_PARAM]), [KVariable('X', sort=INT), KVariable('Y', sort=INT)])
    assert DEFN.add_sort_params(term) == expected
