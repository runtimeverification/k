from __future__ import annotations

import re
from dataclasses import dataclass
from graphlib import TopologicalSorter
from itertools import count
from typing import TYPE_CHECKING

from ..konvert import unmunge
from ..kore.internal import CollectionKind
from ..kore.syntax import SortApp
from ..utils import POSet
from .model import Ctor, ExplBinder, Inductive, Module, Mutual, Signature, Term

if TYPE_CHECKING:
    from typing import Final

    from ..kore.internal import KoreDefn
    from ..kore.syntax import SymbolDecl
    from .model import Command, Declaration


_VALID_LEAN_IDENT: Final = re.compile(
    "_[a-zA-Z0-9_?!']+|[a-zA-Z][a-zA-Z0-9_?!']*"
)  # Simplified to characters permitted in KORE in the first place

_PRELUDE_SORTS: Final = {'SortBool', 'SortBytes', 'SortId', 'SortInt', 'SortString', 'SortStringBuffer'}


@dataclass(frozen=True)
class K2Lean4:
    defn: KoreDefn

    def sort_module(self) -> Module:
        commands: tuple[Command, ...] = tuple(
            block for sorts in _ordered_sorts(self.defn) if (block := self._sort_block(sorts)) is not None
        )
        return Module(commands=commands)

    def _sort_block(self, sorts: list[str]) -> Command | None:
        """Return an optional mutual block or declaration."""
        commands: tuple[Command, ...] = tuple(
            self._transform_sort(sort) for sort in sorts if sort not in _PRELUDE_SORTS
        )

        if not commands:
            return None

        if len(commands) == 1:
            (command,) = commands
            return command

        return Mutual(commands=commands)

    def _transform_sort(self, sort: str) -> Declaration:
        def is_inductive(sort: str) -> bool:
            decl = self.defn.sorts[sort]
            return not decl.hooked and 'hasDomainValues' not in decl.attrs_by_key

        def is_collection(sort: str) -> bool:
            return sort in self.defn.collections

        if is_inductive(sort):
            return self._inductive(sort)

        if is_collection(sort):
            return self._collection(sort)

        raise AssertionError

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
        decl = self.defn.symbols[symbol]
        param_sorts = _param_sorts(decl)
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

    def _collection(self, sort: str) -> Inductive:
        coll = self.defn.collections[sort]
        elem = self.defn.symbols[coll.element]
        sorts = _param_sorts(elem)
        val: Term
        match coll.kind:
            case CollectionKind.LIST:
                (item,) = sorts
                val = Term(f'List {item}')
            case CollectionKind.SET:
                (item,) = sorts
                val = Term(f'List {item}')
            case CollectionKind.MAP:
                key, value = sorts
                val = Term(f'List ({key} × {value})')
        ctor = Ctor('mk', Signature((ExplBinder(('coll',), val),), Term(sort)))
        return Inductive(sort, Signature((), Term('Type')), ctors=(ctor,))


def _param_sorts(decl: SymbolDecl) -> list[str]:
    from ..utils import check_type

    return [check_type(sort, SortApp).name for sort in decl.param_sorts]  # TODO eliminate check_type


def _ordered_sorts(defn: KoreDefn) -> list[list[str]]:
    deps = _sort_dependencies(defn)
    sccs = _sort_sccs(deps)

    sorts_by_scc: dict[int, set[str]] = {}
    for sort, scc in sccs.items():
        sorts_by_scc.setdefault(scc, set()).add(sort)

    scc_deps: dict[int, set[int]] = {}
    for scc, sorts in sorts_by_scc.items():
        assert sorts
        sort, *_ = sorts
        scc_deps[scc] = set()
        for dep in deps[sort]:
            dep_scc = sccs[dep]
            if dep_scc == scc:
                continue
            scc_deps[scc].add(dep_scc)

    ordered_sccs = list(TopologicalSorter(scc_deps).static_order())
    return [sorted(sorts_by_scc[scc]) for scc in ordered_sccs]


def _sort_dependencies(defn: KoreDefn) -> dict[str, set[str]]:
    """Transitively closed sort dependency graph."""
    sorts = defn.sorts
    deps: list[tuple[str, str]] = []
    for sort in sorts:
        # A sort depends on its subsorts (due to inj_{subsort} constructors)
        deps.extend((sort, subsort) for subsort in defn.subsorts.get(sort, []))
        # A sort depends on the parameter sorts of all its constructors
        deps.extend(
            (sort, param_sort)
            for ctor in defn.constructors.get(sort, [])
            for param_sort in _param_sorts(defn.symbols[ctor])
        )
        # If the sort is a collection, the element function parameters are dependencies
        if sort in defn.collections:
            coll = defn.collections[sort]
            elem = defn.symbols[coll.element]
            deps.extend((sort, param_sort) for param_sort in _param_sorts(elem))

    closed = POSet(deps).image  # TODO POSet should be called "transitively closed relation" or similar
    res = {
        sort: set(closed.get(sort, [])) for sort in sorts
    }  # Ensure that sorts without dependencies are also represented
    return res


# TODO Implement a more efficient algorithm, e.g. Tarjan's algorithm
def _sort_sccs(deps: dict[str, set[str]]) -> dict[str, int]:
    res: dict[str, int] = {}

    scc = count()
    for sort, dep_sorts in deps.items():
        if sort in res:
            continue
        idx = next(scc)
        res[sort] = idx
        for dep in dep_sorts:
            if sort in deps[dep]:
                res[dep] = idx

    return res
