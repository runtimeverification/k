from typing import Final, Optional, Tuple, Union

from .syntax import DV, App, LeftAssoc, Pattern, SortApp, String, SymbolId

BOOL: Final = SortApp('SortBool')
INT: Final = SortApp('SortInt')
BYTES: Final = SortApp('SortBytes')
STRING: Final = SortApp('SortString')


def dv(val: Union[bool, int, str]) -> DV:
    if type(val) is bool:
        return bool_dv(val)
    if type(val) is int:
        return int_dv(val)
    if type(val) is str:
        return string_dv(val)
    raise TypeError(f'Illegal type: {type(val)}')


TRUE: Final = DV(BOOL, String('true'))
FALSE: Final = DV(BOOL, String('false'))


def bool_dv(val: bool) -> DV:
    return TRUE if val else FALSE


def int_dv(val: int) -> DV:
    return DV(INT, String(str(val)))


def string_dv(val: str) -> DV:
    return DV(STRING, String(val))


STOP_LIST: Final = App("Lbl'Stop'List")
LBL_LIST: Final = SymbolId("Lbl'Unds'List'Unds'")
LBL_LIST_ITEM: Final = SymbolId('LblListItem')


def kore_list(*args: Pattern) -> Pattern:
    if not args:
        return STOP_LIST
    return LeftAssoc(App(LBL_LIST, args=(App(LBL_LIST_ITEM, args=(arg,)) for arg in args)))


STOP_SET: Final = App("Lbl'Stop'Set")
LBL_SET: Final = SymbolId("Lbl'Unds'Set'Unds'")
LBL_SET_ITEM: Final = SymbolId('LblSetItem')


def kore_set(*args: Pattern) -> Pattern:
    if not args:
        return STOP_SET
    return LeftAssoc(App(LBL_SET, args=(App(LBL_SET_ITEM, args=(arg,)) for arg in args)))


STOP_MAP = App("Lbl'Stop'Map")
LBL_MAP = SymbolId("Lbl'Unds'Map'Unds'")
LBL_MAP_ITEM = SymbolId("Lbl'UndsPipe'-'-GT-Unds'")


def kore_map(*args: Tuple[Pattern, Pattern], cell: Optional[str] = None) -> Pattern:
    if not args:
        return App(f"Lbl'Stop'{cell}Map") if cell else STOP_MAP

    cons_symbol = SymbolId(f"Lbl'Unds'{cell}Map'Unds'") if cell else LBL_MAP
    item_symbol = SymbolId(f'Lbl{cell}MapItem') if cell else LBL_MAP_ITEM
    return LeftAssoc(App(cons_symbol, args=(App(item_symbol, args=arg) for arg in args)))
