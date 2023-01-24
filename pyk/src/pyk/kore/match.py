from typing import Any, Callable, Dict, Optional, Tuple, TypeVar, Union, overload

from ..utils import case, check_type
from .prelude import BOOL, INT, STRING
from .syntax import DV, App, LeftAssoc, Pattern, Sort

T = TypeVar('T')
K = TypeVar('K')
V = TypeVar('V')


def match_dv(pattern: Pattern, sort: Optional[Sort] = None) -> DV:
    dv = check_type(pattern, DV)
    if sort and dv.sort != sort:
        raise ValueError(f'Expected sort {sort.text}, found: {dv.sort.text}')
    return dv


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


def match_list(pattern: Pattern) -> Tuple[Pattern, ...]:
    if type(pattern) is App:
        match_app(pattern, "Lbl'Stop'List")
        return ()

    assoc = match_left_assoc(pattern)
    cons = match_app(assoc.app, "Lbl'Unds'List'Unds'")
    items = (match_app(arg, 'LblListItem') for arg in cons.args)
    elems = (item.args[0] for item in items)
    return tuple(elems)


def match_set(pattern: Pattern) -> Tuple[Pattern, ...]:
    if type(pattern) is App:
        match_app(pattern, "Lbl'Stop'Set")
        return ()

    assoc = match_left_assoc(pattern)
    cons = match_app(assoc.app, "Lbl'Unds'Set'Unds'")
    items = (match_app(arg, 'LblSetItem') for arg in cons.args)
    elems = (item.args[0] for item in items)
    return tuple(elems)


def match_map(pattern: Pattern, *, cell: Optional[str] = None) -> Tuple[Tuple[Pattern, Pattern], ...]:
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
    return tuple(entries)


def kore_bool(pattern: Pattern) -> bool:
    dv = match_dv(pattern, BOOL)
    return bool(dv.value.value)


def kore_int(pattern: Pattern) -> int:
    dv = match_dv(pattern, INT)
    return int(dv.value.value)


def kore_str(pattern: Pattern) -> str:
    dv = match_dv(pattern, STRING)
    return dv.value.value


# Higher-order functions


def app(symbol: Optional[str] = None) -> Callable[[Pattern], App]:
    def res(pattern: Pattern) -> App:
        return match_app(pattern, symbol)

    return res


@overload
def arg(n: int, /) -> Callable[[App], Pattern]:
    ...


@overload
def arg(symbol: str, /) -> Callable[[App], App]:
    ...


def arg(id: Union[int, str]) -> Callable[[App], Union[Pattern, App]]:
    def res(app: App) -> Union[Pattern, App]:
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
def args() -> Callable[[App], Tuple[()]]:
    ...


@overload
def args(n1: int, /) -> Callable[[App], Tuple[Pattern]]:
    ...


@overload
def args(n1: int, n2: int, /) -> Callable[[App], Tuple[Pattern, Pattern]]:
    ...


@overload
def args(n1: int, n2: int, n3: int, /) -> Callable[[App], Tuple[Pattern, Pattern, Pattern]]:
    ...


@overload
def args(n1: int, n2: int, n3: int, n4: int, /) -> Callable[[App], Tuple[Pattern, Pattern, Pattern, Pattern]]:
    ...


@overload
def args(*ns: int) -> Callable[[App], Tuple[Pattern, ...]]:
    ...


@overload
def args(s1: str, /) -> Callable[[App], Tuple[App]]:
    ...


@overload
def args(s1: str, s2: str, /) -> Callable[[App], Tuple[App, App]]:
    ...


@overload
def args(s1: str, s2: str, s3: str, /) -> Callable[[App], Tuple[App, App, App]]:
    ...


@overload
def args(s1: str, s2: str, s3: str, s4: str, /) -> Callable[[App], Tuple[App, App, App, App]]:
    ...


@overload
def args(*ss: str) -> Callable[[App], Tuple[App, ...]]:
    ...


def args(*ids: Any) -> Callable[[App], Tuple]:
    def res(app: App) -> Tuple[Pattern, ...]:
        if not ids:
            return ()

        fst = ids[0]
        if type(fst) is int:
            return tuple(arg(n)(app) for n in ids)

        symbol_match: Dict[str, App] = {}
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


def kore_list_of(item: Callable[[Pattern], T]) -> Callable[[Pattern], Tuple[T, ...]]:
    def res(pattern: Pattern) -> Tuple[T, ...]:
        return tuple(item(e) for e in match_list(pattern))

    return res


def kore_set_of(item: Callable[[Pattern], T]) -> Callable[[Pattern], Tuple[T, ...]]:
    def res(pattern: Pattern) -> Tuple[T, ...]:
        return tuple(item(e) for e in match_set(pattern))

    return res


def kore_map_of(
    key: Callable[[Pattern], K],
    value: Callable[[Pattern], V],
    *,
    cell: Optional[str] = None,
) -> Callable[[Pattern], Tuple[Tuple[K, V], ...]]:
    def res(pattern: Pattern) -> Tuple[Tuple[K, V], ...]:
        return tuple((key(k), value(v)) for k, v in match_map(pattern, cell=cell))

    return res


def case_symbol(
    *cases: Tuple[str, Callable[[App], T]],
    default: Optional[Callable[[App], T]] = None,
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
