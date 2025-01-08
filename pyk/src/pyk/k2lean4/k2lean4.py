from __future__ import annotations

import re
from dataclasses import dataclass
from typing import TYPE_CHECKING

from ..konvert import unmunge
from ..kore.internal import CollectionKind
from ..kore.syntax import SortApp
from ..utils import check_type
from .model import Abbrev, Ctor, ExplBinder, Inductive, Module, Signature, Term

if TYPE_CHECKING:
    from typing import Final

    from ..kore.internal import KoreDefn
    from .model import Command


_VALID_LEAN_IDENT: Final = re.compile(
    "_[a-zA-Z0-9_?!']+|[a-zA-Z][a-zA-Z0-9_?!']*"
)  # Simplified to characters permitted in KORE in the first place


@dataclass(frozen=True)
class K2Lean4:
    defn: KoreDefn

    def sort_module(self) -> Module:
        commands = []
        commands += self._inductives()
        commands += self._collections()
        return Module(commands=commands)

    def _inductives(self) -> list[Command]:
        def is_inductive(sort: str) -> bool:
            decl = self.defn.sorts[sort]
            return not decl.hooked and 'hasDomainValues' not in decl.attrs_by_key

        sorts = sorted(sort for sort in self.defn.sorts if is_inductive(sort))
        return [self._inductive(sort) for sort in sorts]

    def _inductive(self, sort: str) -> Inductive:
        subsorts = sorted(self.defn.subsorts.get(sort, ()))
        symbols = sorted(self.defn.constructors.get(sort, ()))
        ctors: list[Ctor] = []
        ctors.extend(self._inj_ctor(sort, subsort) for subsort in subsorts)
        ctors.extend(self._symbol_ctor(sort, symbol) for symbol in symbols)
        return Inductive(sort, Signature((), Term('Type')), ctors=ctors)

    def _inj_ctor(self, sort: str, subsort: str) -> Ctor:
        return Ctor(f'inj_{subsort}', Signature((ExplBinder(('x',), Term(subsort)),), Term(sort)))

    def _symbol_ctor(self, sort: str, symbol: str) -> Ctor:
        param_sorts = (
            check_type(sort, SortApp).name for sort in self.defn.symbols[symbol].param_sorts
        )  # TODO eliminate check_type
        symbol = self._symbol_ident(symbol)
        binders = tuple(ExplBinder((f'x{i}',), Term(sort)) for i, sort in enumerate(param_sorts))
        return Ctor(symbol, Signature(binders, Term(sort)))

    @staticmethod
    def _symbol_ident(symbol: str) -> str:
        if symbol.startswith('Lbl'):
            symbol = symbol[3:]
        symbol = unmunge(symbol)
        if not _VALID_LEAN_IDENT.fullmatch(symbol):
            symbol = f'«{symbol}»'
        return symbol

    def _collections(self) -> list[Command]:
        return [self._collection(sort) for sort in sorted(self.defn.collections)]

    def _collection(self, sort: str) -> Abbrev:
        coll = self.defn.collections[sort]
        elem = self.defn.symbols[coll.element]
        sorts = ' '.join(check_type(sort, SortApp).name for sort in elem.param_sorts)  # TODO eliminate check_type
        assert sorts
        match coll.kind:
            case CollectionKind.LIST:
                val = Term(f'ListHook {sorts}')
            case CollectionKind.MAP:
                val = Term(f'MapHook {sorts}')
            case CollectionKind.SET:
                val = Term(f'SetHook {sorts}')
        return Abbrev(sort, val, Signature((), Term('Type')))
