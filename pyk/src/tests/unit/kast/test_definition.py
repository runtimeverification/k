from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.att import Atts, KAtt
from pyk.kast.inner import KApply, KSort, KVariable
from pyk.kast.outer import KDefinition, KFlatModule, KNonTerminal, KProduction, KTerminal

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast.inner import KInner


# ---------------------------------------------------------------------------
# Minimal test definition
#
# Cell map fragment:
#   AccountCellMap ::= AccountCellMap AccountCellMap  [cellCollection, element(AccountCellMapItem), wrapElement(<account>)]
#   AccountCellMap ::= AccountCellMapItem(Int, AccountCell)
#   AccountCell    ::= <account>(Int, Int)
#   AccountCell    ::= getEntry(AccountCell)           -- takes element sort, NOT map sort
# ---------------------------------------------------------------------------

INT: Final = KSort('Int')
ACCOUNT_CELL_MAP: Final = KSort('AccountCellMap')
ACCOUNT_CELL: Final = KSort('AccountCell')

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
    [KFlatModule('TEST', [_ACCT_MAP_CONCAT, _ACCT_MAP_ITEM, _ACCOUNT_CELL, _GET_ENTRY])],
)

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
