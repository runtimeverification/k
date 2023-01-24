from typing import Final, Optional, Tuple, Union

from .syntax import DV, App, LeftAssoc, Pattern, SortApp, String

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


def bool_dv(val: bool) -> DV:
    return DV(BOOL, String('true' if val else 'false'))


def int_dv(val: int) -> DV:
    return DV(INT, String(str(val)))


def string_dv(val: str) -> DV:
    return DV(STRING, String(val))


def kore_list(*args: Pattern) -> Pattern:
    if not args:
        return App("Lbl'Stop'List")
    return LeftAssoc(App("Lbl'Unds'List'Unds'", args=(App('LblListItem', args=(arg,)) for arg in args)))


def kore_set(*args: Pattern) -> Pattern:
    if not args:
        return App("Lbl'Stop'Set")
    return LeftAssoc(App("Lbl'Unds'Set'Unds'", args=(App('LblSetItem', args=(arg,)) for arg in args)))


def kore_map(*args: Tuple[Pattern, Pattern], cell: Optional[str] = None) -> Pattern:
    cell = cell or ''
    stop_symbol = f"Lbl'Stop'{cell}Map"
    cons_symbol = f"Lbl'Unds'{cell}Map'Unds'"
    item_symbol = "Lbl'UndsPipe'-'-GT-Unds'" if not cell else f'Lbl{cell}MapItem'
    if not args:
        return App(stop_symbol)
    return LeftAssoc(App(cons_symbol, args=(App(item_symbol, args=arg) for arg in args)))
