from __future__ import annotations

from itertools import chain
from typing import TYPE_CHECKING

from ..dequote import bytes_decode
from ..utils import check_type
from .syntax import DV, App, LeftAssoc, RightAssoc, SortApp, String, SymbolId

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator, Mapping
    from typing import Any, Final

    from .syntax import EVar, Pattern, Sort


# ----------
# Base types
# ----------

BOOL: Final = SortApp('SortBool')
INT: Final = SortApp('SortInt')
BYTES: Final = SortApp('SortBytes')
STRING: Final = SortApp('SortString')
ID: Final = SortApp('SortId')

TRUE: Final = DV(BOOL, String('true'))
FALSE: Final = DV(BOOL, String('false'))


def dv(val: bool | int | bytes | str) -> DV:
    if type(val) is bool:
        return bool_dv(val)
    if type(val) is int:
        return int_dv(val)
    if type(val) is bytes:
        return bytes_dv(val)
    if type(val) is str:
        return str_dv(val)
    raise TypeError(f'Illegal type: {type(val)}')


def bool_dv(val: bool) -> DV:
    return TRUE if val else FALSE


def int_dv(val: int) -> DV:
    return DV(INT, String(str(val)))


def bytes_dv(val: bytes) -> DV:
    return DV(BYTES, String(bytes_decode(val)))


def str_dv(val: str) -> DV:
    return DV(STRING, String(val))


# ------------
# Bool
# ------------

LBL_NOT_BOOL: Final = SymbolId("LblnotBool'Unds'")
LBL_AND_BOOL: Final = SymbolId("Lbl'Unds'andBool'Unds'")
LBL_OR_BOOL: Final = SymbolId("Lbl'Unds'orBool'Unds'")
LBL_IMPLIES_BOOL: Final = SymbolId("Lbl'Unds'impliesBool'Unds'")
LBL_XOR_BOOL: Final = SymbolId("Lbl'Unds'xorBool'Unds'")
LBL_EQ_BOOL: Final = SymbolId("Lbl'UndsEqlsEqls'Bool'Unds'")
LBL_NE_BOOL: Final = SymbolId("Lbl'UndsEqlsSlshEqls'Bool'Unds'")


def not_bool(pattern: Pattern) -> Pattern:
    return App(LBL_NOT_BOOL, (), (pattern,))


def and_bool(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_AND_BOOL, (), (left, right))


def or_bool(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_OR_BOOL, (), (left, right))


def implies_bool(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_IMPLIES_BOOL, (), (left, right))


def xor_bool(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_XOR_BOOL, (), (left, right))


def eq_bool(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_EQ_BOOL, (), (left, right))


def ne_bool(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_NE_BOOL, (), (left, right))


# ------------
# Int
# ------------

LBL_EQ_INT: Final = SymbolId("Lbl'UndsEqlsEqls'Int'Unds'")
LBL_NE_INT: Final = SymbolId("Lbl'UndsEqlsSlshEqls'Int'Unds'")
LBL_GT_INT: Final = SymbolId("Lbl'Unds-GT-'Int'Unds'")
LBL_GE_INT: Final = SymbolId("Lbl'Unds-GT-Eqls'Int'Unds'")
LBL_LT_INT: Final = SymbolId("Lbl'Unds-LT-'Int'Unds'")
LBL_LE_INT: Final = SymbolId("Lbl'Unds-LT-Eqls'Int'Unds'")


def eq_int(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_EQ_INT, (), (left, right))


def ne_int(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_NE_INT, (), (left, right))


def gt_int(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_GT_INT, (), (left, right))


def ge_int(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_GE_INT, (), (left, right))


def lt_int(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_LT_INT, (), (left, right))


def le_int(left: Pattern, right: Pattern) -> Pattern:
    return App(LBL_LE_INT, (), (left, right))


# ------------
# K constructs
# ------------

# TODO auto injections

SORT_K: Final = SortApp('SortK')
SORT_K_ITEM: Final = SortApp('SortKItem')
SORT_K_CONFIG_VAR: Final = SortApp('SortKConfigVar')
SORT_GENERATED_TOP_CELL: Final = SortApp('SortGeneratedTopCell')
SORT_GENERATED_COUNTER_CELL: Final = SortApp('SortGeneratedCounterCell')

LBL_INIT_GENERATED_TOP_CELL: Final = SymbolId('LblinitGeneratedTopCell')
LBL_GENERATED_TOP: Final = SymbolId("Lbl'-LT-'generatedTop'-GT-'")
LBL_GENERATED_COUNTER: Final = SymbolId("Lbl'-LT-'generatedCounter'-GT-'")
LBL_K: Final = SymbolId("Lbl'-LT-'k'-GT-'")
LBL_ITE: Final = SymbolId('Lblite')
INJ: Final = SymbolId('inj')
KSEQ: Final = SymbolId('kseq')

DOTK: Final = App('dotk', (), ())


def init_generated_top_cell(pattern: Pattern) -> App:
    return App(LBL_INIT_GENERATED_TOP_CELL, (), (pattern,))


def generated_top(patterns: Iterable[Pattern]) -> App:
    return App(LBL_GENERATED_TOP, (), patterns)


def generated_counter(pattern: Pattern) -> App:
    return App(LBL_GENERATED_COUNTER, (), (pattern,))


def k(pattern: Pattern) -> App:
    return App(LBL_K, (), (pattern,))


def inj(sort1: Sort, sort2: Sort, pattern: Pattern) -> App:
    return App(INJ, (sort1, sort2), (pattern,))


def kseq(kitems: Iterable[Pattern], *, dotvar: EVar | None = None) -> Pattern:
    if dotvar and dotvar.sort != SORT_K:
        raise ValueError(f'Expected {SORT_K.text} as dotvar sort, got: {dotvar.sort.text}')

    tail = dotvar or DOTK
    args = tuple(chain(kitems, (tail,)))

    if len(args) == 1:
        return tail

    if len(args) == 2:
        return App(KSEQ, (), args)

    return RightAssoc(KSEQ, (), args)


def k_config_var(var: str) -> DV:
    return DV(SORT_K_CONFIG_VAR, String(var))


def top_cell_initializer(config: Mapping[str, Pattern]) -> App:
    return init_generated_top_cell(
        map_pattern(
            *(
                (
                    inj(SORT_K_CONFIG_VAR, SORT_K_ITEM, k_config_var(key)),
                    value,
                )
                for key, value in config.items()
            )
        )
    )


# -----------
# Collections
# -----------

STOP_LIST: Final = App("Lbl'Stop'List")
LBL_LIST: Final = SymbolId("Lbl'Unds'List'Unds'")
LBL_LIST_ITEM: Final = SymbolId('LblListItem')


def list_pattern(*args: Pattern) -> Pattern:
    if not args:
        return STOP_LIST
    return LeftAssoc(LBL_LIST, args=(App(LBL_LIST_ITEM, args=(arg,)) for arg in args))


STOP_SET: Final = App("Lbl'Stop'Set")
LBL_SET: Final = SymbolId("Lbl'Unds'Set'Unds'")
LBL_SET_ITEM: Final = SymbolId('LblSetItem')


def set_pattern(*args: Pattern) -> Pattern:
    if not args:
        return STOP_SET
    return LeftAssoc(LBL_SET, args=(App(LBL_SET_ITEM, args=(arg,)) for arg in args))


STOP_MAP: Final = App("Lbl'Stop'Map")
LBL_MAP: Final = SymbolId("Lbl'Unds'Map'Unds'")
LBL_MAP_ITEM: Final = SymbolId("Lbl'UndsPipe'-'-GT-Unds'")


def map_pattern(*args: tuple[Pattern, Pattern], cell: str | None = None) -> Pattern:
    if not args:
        return App(f"Lbl'Stop'{cell}Map") if cell else STOP_MAP

    cons_symbol = SymbolId(f"Lbl'Unds'{cell}Map'Unds'") if cell else LBL_MAP
    item_symbol = SymbolId(f'Lbl{cell}MapItem') if cell else LBL_MAP_ITEM
    return LeftAssoc(cons_symbol, args=(App(item_symbol, args=arg) for arg in args))


STOP_RANGEMAP: Final = App("Lbl'Stop'RangeMap")
LBL_RANGEMAP: Final = SymbolId("Lbl'Unds'RangeMap'Unds'")
LBL_RANGEMAP_ITEM: Final = SymbolId("Lbl'Unds'r'Pipe'-'-GT-Unds'")
LBL_RANGEMAP_RANGE: Final = SymbolId("LblRangeMap'Coln'Range")


def rangemap_pattern(*args: tuple[tuple[Pattern, Pattern], Pattern]) -> Pattern:
    if not args:
        return STOP_RANGEMAP

    return LeftAssoc(
        LBL_RANGEMAP,
        args=(App(LBL_RANGEMAP_ITEM, args=(App(LBL_RANGEMAP_RANGE, args=arg[0]), arg[1])) for arg in args),
    )


# ----
# JSON
# ----

SORT_JSON: Final = SortApp('SortJSON')
SORT_JSON_KEY: Final = SortApp('SortJSONKey')

LBL_JSONS: Final = SymbolId('LblJSONs')
LBL_JSON_LIST: Final = SymbolId('LblJSONList')
LBL_JSON_OBJECT: Final = SymbolId('LblJSONObject')
LBL_JSON_ENTRY: Final = SymbolId('LblJSONEntry')

JSON_NULL: Final = App('LblJSONnull')
STOP_JSONS: Final = App("Lbl'Stop'List'LBraQuot'JSONs'QuotRBra'")

LBL_STRING2JSON: Final = SymbolId('LblString2JSON')
LBL_JSON2STRING: Final = SymbolId('LblJSON2String')


def string2json(pattern: Pattern) -> App:
    return App(LBL_STRING2JSON, (), (pattern,))


def json2string(pattern: Pattern) -> App:
    return App(LBL_JSON2STRING, (), (pattern,))


def json_list(pattern: Pattern) -> App:
    return App(LBL_JSON_LIST, (), (pattern,))


def json_object(pattern: Pattern) -> App:
    return App(LBL_JSON_OBJECT, (), (pattern,))


def jsons(patterns: Iterable[Pattern]) -> RightAssoc:
    return RightAssoc(LBL_JSONS, (), chain(patterns, (STOP_JSONS,)))


def json_key(key: str) -> App:
    return inj(STRING, SORT_JSON_KEY, str_dv(key))


def json_entry(key: Pattern, value: Pattern) -> App:
    return App(LBL_JSON_ENTRY, (), (key, value))


def json_to_kore(data: Any) -> Pattern:
    match data:
        case None:
            return JSON_NULL
        case bool():
            return inj(BOOL, SORT_JSON, bool_dv(data))
        case int():
            return inj(INT, SORT_JSON, int_dv(data))
        case str():
            return inj(STRING, SORT_JSON, str_dv(data))
        case list():
            return json_list(jsons(json_to_kore(elem) for elem in data))
        case dict():
            return json_object(
                jsons(json_entry(json_key(check_type(key, str)), json_to_kore(value)) for key, value in data.items())
            )
        case _:
            raise TypeError(f'Unsupported object of type: {type(data).__name__}: {data}')


# TODO Eliminate circularity with kore.match
def kore_to_json(pattern: Pattern) -> Any:
    from . import match as km

    if isinstance(pattern, DV):
        if pattern.sort == BOOL:
            return km.kore_bool(pattern)

        if pattern.sort == INT:
            return km.kore_int(pattern)

        if pattern.sort == STRING:
            return km.kore_str(pattern)

    if isinstance(pattern, App):
        if pattern.symbol == JSON_NULL.symbol:
            return None

        if pattern.symbol == INJ.value:  # can be further refined: arg is DV, ...
            return kore_to_json(km.inj(pattern))

        if pattern.symbol == LBL_JSON_LIST.value:
            return [kore_to_json(elem) for elem in _iter_json_list(pattern)]

        if pattern.symbol == LBL_JSON_OBJECT.value:
            return {key: kore_to_json(value) for key, value in _iter_json_object(pattern)}

    raise ValueError(f'Not a JSON pattern: {pattern.text}')


def _iter_json_list(app: App) -> Iterator[Pattern]:
    from . import match as km

    km.match_app(app, LBL_JSON_LIST.value)
    curr = km.match_app(app.args[0])
    while curr.symbol != STOP_JSONS.symbol:
        km.match_app(curr, LBL_JSONS.value)
        yield curr.args[0]
        curr = km.match_app(curr.args[1])


def _iter_json_object(app: App) -> Iterator[tuple[str, Pattern]]:
    from . import match as km

    km.match_app(app, LBL_JSON_OBJECT.value)
    curr = km.match_app(app.args[0])
    while curr.symbol != STOP_JSONS.symbol:
        km.match_app(curr, LBL_JSONS.value)
        entry = km.match_app(curr.args[0], LBL_JSON_ENTRY.value)
        key = km.kore_str(km.inj(entry.args[0]))
        value = entry.args[1]
        yield key, value
        curr = km.match_app(curr.args[1])
