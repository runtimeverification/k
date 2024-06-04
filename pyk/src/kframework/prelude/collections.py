from __future__ import annotations

from typing import TYPE_CHECKING

from ..kast.inner import KApply, KLabel, KSort, build_assoc

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from ..kast import KInner

SET: Final = KSort('Set')
LIST: Final = KSort('List')
MAP: Final = KSort('Map')
BAG: Final = KSort('Bag')


def set_empty() -> KInner:
    return KApply('.Set')


def set_item(k: KInner) -> KInner:
    return KApply('SetItem', [k])


def set_of(ks: Iterable[KInner]) -> KInner:
    return build_assoc(set_empty(), KLabel('_Set_'), map(set_item, ks))


def list_empty() -> KInner:
    return KApply('.List')


def list_item(k: KInner) -> KInner:
    return KApply('ListItem', [k])


def list_of(ks: Iterable[KInner]) -> KInner:
    return build_assoc(list_empty(), KLabel('_List_'), map(list_item, ks))


def map_empty() -> KInner:
    return KApply('.Map')


def map_item(k: KInner, v: KInner) -> KInner:
    return KApply('_|->_', [k, v])


def map_of(ks: dict[KInner, KInner] | Iterable[tuple[KInner, KInner]]) -> KInner:
    ks = dict(ks)
    return build_assoc(map_empty(), KLabel('_Map_'), (map_item(k, v) for k, v in ks.items()))
