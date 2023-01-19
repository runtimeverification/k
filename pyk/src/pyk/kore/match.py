from typing import Optional, Tuple

from ..utils import check_type
from .prelude import BOOL, INT, STRING
from .syntax import DV, App, LeftAssoc, Pattern, Sort


def match_dv(pattern: Pattern, sort: Optional[Sort] = None) -> DV:
    dv = check_type(pattern, DV)
    if sort and dv.sort != sort:
        raise ValueError(f'Expected sort {sort.text}, found: {dv.sort.text}')
    return dv


def match_bool(pattern: Pattern) -> bool:
    dv = match_dv(pattern, BOOL)
    return bool(dv.value.value)


def match_int(pattern: Pattern) -> int:
    dv = match_dv(pattern, INT)
    return int(dv.value.value)


def match_str(pattern: Pattern) -> str:
    dv = match_dv(pattern, STRING)
    return dv.value.value


def match_symbol(app: App, symbol: str) -> None:
    if app.symbol != symbol:
        raise ValueError(f'Expected symbol {symbol}, found: {app.symbol}')


def match_app(pattern: Pattern, symbol: Optional[str] = None) -> App:
    app = check_type(pattern, App)
    if symbol is not None:
        match_symbol(app, symbol)
    return app


def match_inj(pattern: Pattern) -> App:
    return match_app(pattern, 'inj')


def match_left_assoc(pattern: Pattern) -> LeftAssoc:
    return check_type(pattern, LeftAssoc)


def match_list(pattern: Pattern, *, inj_items: bool = False) -> Tuple[Pattern, ...]:
    if type(pattern) is App:
        match_app(pattern, "Lbl'Stop'List")
        return ()

    assoc = match_left_assoc(pattern)
    cons = match_app(assoc.app, "Lbl'Unds'List'Unds'")
    items = (match_app(arg, 'LblListItem') for arg in cons.args)
    elems = (item.args[0] for item in items)

    if inj_items:
        elems = (match_inj(elem).args[0] for elem in elems)

    return tuple(elems)


def match_set(pattern: Pattern, *, inj_items: bool = False) -> Tuple[Pattern, ...]:
    if type(pattern) is App:
        match_app(pattern, "Lbl'Stop'Set")
        return ()

    assoc = match_left_assoc(pattern)
    cons = match_app(assoc.app, "Lbl'Unds'Set'Unds'")
    items = (match_app(arg, 'LblSetItem') for arg in cons.args)
    elems = (item.args[0] for item in items)

    if inj_items:
        elems = (match_inj(elem).args[0] for elem in elems)

    return tuple(elems)


def match_map(
    pattern: Pattern,
    *,
    cell: Optional[str] = None,
    inj_keys: bool = False,
    inj_values: bool = False,
) -> Tuple[Tuple[Pattern, Pattern], ...]:
    cell = cell or ''
    stop_symbol = f"Lbl'Stop'{cell}Map"
    cons_symbol = f"Lbl'Unds'{cell}Map'Unds'"
    item_symbol = "Lbl'UndsPipe'-'-GT-Unds'" if not cell else f'Lbl{cell}MapItem'

    if type(pattern) is App:
        match_app(pattern, stop_symbol)
        return ()

    assoc = match_left_assoc(pattern)
    cons = match_app(assoc.app, cons_symbol)
    items = (match_app(arg, item_symbol) for arg in cons.args)
    entries = ((item.args[0], item.args[1]) for item in items)

    if inj_keys:
        entries = ((match_inj(key).args[0], value) for key, value in entries)

    if inj_values:
        entries = ((key, match_inj(value).args[0]) for key, value in entries)

    return tuple(entries)
