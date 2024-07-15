from __future__ import annotations

from typing import TYPE_CHECKING, overload

from ..dequote import bytes_encode
from ..utils import case, check_type
from .prelude import BOOL, BYTES, ID, INT, STRING
from .syntax import DV, App, LeftAssoc

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Any, TypeVar

    from .syntax import Pattern, Sort

    T = TypeVar('T')
    K = TypeVar('K')
    V = TypeVar('V')


def match_dv(pattern: Pattern, sort: Sort | None = None) -> DV:
    dv = check_type(pattern, DV)
    if sort and dv.sort != sort:
        raise ValueError(f'Expected sort {sort.text}, found: {dv.sort.text}')
    return dv


def match_symbol(actual: str, expected: str) -> None:
    if actual != expected:
        raise ValueError(f'Expected symbol {expected}, found: {actual}')


def match_app(pattern: Pattern, symbol: str | None = None) -> App:
    app = check_type(pattern, App)
    if symbol is not None:
        match_symbol(app.symbol, symbol)
    return app


def match_inj(pattern: Pattern) -> App:
    return match_app(pattern, 'inj')


def match_left_assoc(pattern: Pattern, symbol: str | None = None) -> LeftAssoc:
    assoc = check_type(pattern, LeftAssoc)
    if symbol is not None:
        match_symbol(assoc.symbol, symbol)
    return assoc


def match_list(pattern: Pattern) -> tuple[Pattern, ...]:
    if type(pattern) is App:
        match_app(pattern, "Lbl'Stop'List")
        return ()

    assoc = match_left_assoc(pattern, "Lbl'Unds'List'Unds'")
    items = (match_app(arg, 'LblListItem') for arg in assoc.args)
    elems = (item.args[0] for item in items)
    return tuple(elems)


def match_set(pattern: Pattern) -> tuple[Pattern, ...]:
    if type(pattern) is App:
        match_app(pattern, "Lbl'Stop'Set")
        return ()

    assoc = match_left_assoc(pattern, "Lbl'Unds'Set'Unds'")
    items = (match_app(arg, 'LblSetItem') for arg in assoc.args)
    elems = (item.args[0] for item in items)
    return tuple(elems)


def match_map(pattern: Pattern, *, cell: str | None = None) -> tuple[tuple[Pattern, Pattern], ...]:
    cell = cell or ''
    stop_symbol = f"Lbl'Stop'{cell}Map"
    cons_symbol = f"Lbl'Unds'{cell}Map'Unds'"
    item_symbol = "Lbl'UndsPipe'-'-GT-Unds'" if not cell else f'Lbl{cell}MapItem'

    if type(pattern) is App:
        match_app(pattern, stop_symbol)
        return ()

    assoc = match_left_assoc(pattern, cons_symbol)
    items = (match_app(arg, item_symbol) for arg in assoc.args)
    entries = ((item.args[0], item.args[1]) for item in items)
    return tuple(entries)


def match_rangemap(pattern: Pattern) -> tuple[tuple[tuple[Pattern, Pattern], Pattern], ...]:
    stop_symbol = "Lbl'Stop'RangeMap"
    cons_symbol = "Lbl'Unds'RangeMap'Unds'"
    item_symbol = "Lbl'Unds'r'Pipe'-'-GT-Unds'"

    if type(pattern) is App:
        match_app(pattern, stop_symbol)
        return ()

    assoc = match_left_assoc(pattern)
    cons = match_app(assoc.app, cons_symbol)
    items = (match_app(arg, item_symbol) for arg in cons.args)
    entries = ((_match_range(item.args[0]), item.args[1]) for item in items)
    return tuple(entries)


def _match_range(pattern: Pattern) -> tuple[Pattern, Pattern]:
    range_symbol = "LblRangeMap'Coln'Range"
    range = match_app(pattern, range_symbol)
    return (range.args[0], range.args[1])


def kore_bool(pattern: Pattern) -> bool:
    dv = match_dv(pattern, BOOL)
    match dv.value.value:
        case 'true':
            return True
        case 'false':
            return False
        case _:
            raise ValueError(f'Invalid Boolean domain value: {dv.text}')


def kore_int(pattern: Pattern) -> int:
    dv = match_dv(pattern, INT)
    return int(dv.value.value)


def kore_bytes(pattern: Pattern) -> bytes:
    dv = match_dv(pattern, BYTES)
    return bytes_encode(dv.value.value)


def kore_str(pattern: Pattern) -> str:
    dv = match_dv(pattern, STRING)
    return dv.value.value


def kore_id(pattern: Pattern) -> str:
    dv = match_dv(pattern, ID)
    return dv.value.value


# Higher-order functions


def app(symbol: str | None = None) -> Callable[[Pattern], App]:
    def res(pattern: Pattern) -> App:
        return match_app(pattern, symbol)

    return res


@overload
def arg(n: int, /) -> Callable[[App], Pattern]: ...


@overload
def arg(symbol: str, /) -> Callable[[App], App]: ...


def arg(id: int | str) -> Callable[[App], Pattern | App]:
    def res(app: App) -> Pattern | App:
        if type(id) is int:
            if len(app.args) <= id:
                raise ValueError('Argument index is out of range')

            return app.args[id]

        try:
            arg, *_ = (arg for arg in app.args if type(arg) is App and arg.symbol == id)
        except ValueError:
            raise ValueError(f'No matching argument found for symbol: {id}') from None
        return arg

    return res


@overload
def args() -> Callable[[App], tuple[()]]: ...


@overload
def args(n1: int, /) -> Callable[[App], tuple[Pattern]]: ...


@overload
def args(n1: int, n2: int, /) -> Callable[[App], tuple[Pattern, Pattern]]: ...


@overload
def args(n1: int, n2: int, n3: int, /) -> Callable[[App], tuple[Pattern, Pattern, Pattern]]: ...


@overload
def args(n1: int, n2: int, n3: int, n4: int, /) -> Callable[[App], tuple[Pattern, Pattern, Pattern, Pattern]]: ...


@overload
def args(*ns: int) -> Callable[[App], tuple[Pattern, ...]]: ...


@overload
def args(s1: str, /) -> Callable[[App], tuple[App]]: ...


@overload
def args(s1: str, s2: str, /) -> Callable[[App], tuple[App, App]]: ...


@overload
def args(s1: str, s2: str, s3: str, /) -> Callable[[App], tuple[App, App, App]]: ...


@overload
def args(s1: str, s2: str, s3: str, s4: str, /) -> Callable[[App], tuple[App, App, App, App]]: ...


@overload
def args(*ss: str) -> Callable[[App], tuple[App, ...]]: ...


def args(*ids: Any) -> Callable[[App], tuple]:
    def res(app: App) -> tuple[Pattern, ...]:
        if not ids:
            return ()

        fst = ids[0]
        if type(fst) is int:
            return tuple(arg(n)(app) for n in ids)

        symbol_match: dict[str, App] = {}
        symbols = set(ids)

        for _arg in app.args:
            if type(_arg) is App and _arg.symbol in symbols and _arg.symbol not in symbol_match:
                symbol_match[_arg.symbol] = _arg

            if len(symbol_match) == len(symbols):
                return tuple(symbol_match[symbol] for symbol in ids)

        unmatched_symbols = symbols - set(symbol_match)
        assert unmatched_symbols
        unmatched_symbol_str = ', '.join(unmatched_symbols)
        raise ValueError(f'No matching arguments found for symbols: {unmatched_symbol_str}')

    return res


def inj(pattern: Pattern) -> Pattern:
    return arg(0)(app('inj')(pattern))


def kore_list_of(item: Callable[[Pattern], T]) -> Callable[[Pattern], tuple[T, ...]]:
    def res(pattern: Pattern) -> tuple[T, ...]:
        return tuple(item(e) for e in match_list(pattern))

    return res


def kore_set_of(item: Callable[[Pattern], T]) -> Callable[[Pattern], tuple[T, ...]]:
    def res(pattern: Pattern) -> tuple[T, ...]:
        return tuple(item(e) for e in match_set(pattern))

    return res


def kore_map_of(
    key: Callable[[Pattern], K],
    value: Callable[[Pattern], V],
    *,
    cell: str | None = None,
) -> Callable[[Pattern], tuple[tuple[K, V], ...]]:
    def res(pattern: Pattern) -> tuple[tuple[K, V], ...]:
        return tuple((key(k), value(v)) for k, v in match_map(pattern, cell=cell))

    return res


def kore_rangemap_of(
    key: Callable[[Pattern], K],
    value: Callable[[Pattern], V],
) -> Callable[[Pattern], tuple[tuple[tuple[K, K], V], ...]]:
    def res(pattern: Pattern) -> tuple[tuple[tuple[K, K], V], ...]:
        return tuple(((key(k[0]), key(k[1])), value(v)) for k, v in match_rangemap(pattern))

    return res


def case_symbol(
    *cases: tuple[str, Callable[[App], T]],
    default: Callable[[App], T] | None = None,
) -> Callable[[Pattern], T]:
    def cond(symbol: str) -> Callable[[App], bool]:
        return lambda app: app.symbol == symbol

    def res(pattern: Pattern) -> T:
        app = match_app(pattern)
        return case(
            cases=((cond(symbol), then) for symbol, then in cases),
            default=default,
        )(app)

    return res
