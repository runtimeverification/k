from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from functools import cached_property
from typing import TYPE_CHECKING, NamedTuple, final

from ..utils import FrozenDict, POSet, check_type
from .manip import collect_symbols
from .rule import FunctionRule, RewriteRule, Rule
from .syntax import App, Axiom, SortApp, SortDecl, String, Symbol, SymbolDecl

if TYPE_CHECKING:
    from collections.abc import Iterable

    from .syntax import Definition, Pattern


class CollectionKind(Enum):
    LIST = 'List'
    MAP = 'Map'
    SET = 'Set'


class Collection(NamedTuple):
    sort: str
    concat: str
    element: str
    unit: str
    kind: CollectionKind

    @staticmethod
    def from_decl(decl: SortDecl) -> Collection:
        if not 'element' in decl.attrs_by_key:
            raise ValueError(f'Not a sort declaration: {decl.text}')
        sort = decl.name
        concat = Collection._extract_label(decl, 'concat')
        element = Collection._extract_label(decl, 'element')
        unit = Collection._extract_label(decl, 'unit')
        kind = CollectionKind(Collection._extract_string(decl, 'hook').split('.')[1])  # 'MAP.Map' -> CollectionKind.MAP
        return Collection(
            sort=sort,
            concat=concat,
            element=element,
            unit=unit,
            kind=kind,
        )

    @staticmethod
    def _extract_label(decl: SortDecl, attr: str) -> str:
        match decl.attrs_by_key[attr]:
            case App(attr, args=(App(res),)):
                return res
            case _:
                raise AssertionError()

    @staticmethod
    def _extract_string(decl: SortDecl, attr: str) -> str:
        match decl.attrs_by_key[attr]:
            case App(attr, args=(String(res),)):
                return res
            case _:
                raise AssertionError()


@final
@dataclass(frozen=True)
class KoreDefn:
    sorts: FrozenDict[str, SortDecl]
    symbols: FrozenDict[str, SymbolDecl]
    subsorts: FrozenDict[str, frozenset[str]]
    rewrites: tuple[RewriteRule, ...]
    functions: FrozenDict[str, tuple[FunctionRule, ...]]

    @staticmethod
    def from_definition(defn: Definition) -> KoreDefn:
        sorts: dict[str, SortDecl] = {}
        symbols: dict[str, SymbolDecl] = {}
        subsorts: list[tuple[str, str]] = []
        rewrites: list[RewriteRule] = []
        functions: dict[str, list[FunctionRule]] = {}

        for sent in defn.sentences:
            match sent:
                case SortDecl(name):
                    sorts[name] = sent
                case SymbolDecl(Symbol(name)):
                    symbols[name] = sent
                    if 'function' in sent.attrs_by_key:
                        functions.setdefault(name, [])
                case Axiom(attrs=(App('subsort', (SortApp(subsort), SortApp(supersort))),)):
                    subsorts.append((subsort, supersort))
                case Axiom():
                    if Rule.is_rule(sent):
                        rule = Rule.from_axiom(sent)
                        if isinstance(rule, RewriteRule):
                            rewrites.append(rule)
                        elif isinstance(rule, FunctionRule):
                            functions.setdefault(rule.lhs.symbol, []).append(rule)

        return KoreDefn(
            sorts=FrozenDict(sorts),
            symbols=FrozenDict(symbols),
            subsorts=POSet((supersort, subsort) for subsort, supersort in subsorts).image,
            rewrites=tuple(rewrites),
            functions=FrozenDict((key, tuple(values)) for key, values in functions.items()),
        )

    @cached_property
    def constructors(self) -> FrozenDict[str, tuple[str, ...]]:
        grouped: dict[str, list[str]] = {}
        for symbol, decl in self.symbols.items():
            if not 'constructor' in decl.attrs_by_key:
                continue
            sort = check_type(decl.sort, SortApp).name  # TODO eliminate by further processing the SortDecl
            grouped.setdefault(sort, []).append(symbol)
        return FrozenDict((sort, tuple(symbols)) for sort, symbols in grouped.items())

    @cached_property
    def collections(self) -> FrozenDict[str, Collection]:
        colls: dict[str, Collection] = {}
        for sort, decl in self.sorts.items():
            if not 'element' in decl.attrs_by_key:
                continue
            coll = Collection.from_decl(decl)
            assert sort == coll.sort
            colls[sort] = coll
        return FrozenDict(colls)

    def let(
        self,
        *,
        sorts: FrozenDict[str, SortDecl] | None = None,
        symbols: FrozenDict[str, SymbolDecl] | None = None,
        subsorts: FrozenDict[str, frozenset[str]] | None = None,
        rewrites: tuple[RewriteRule, ...] | None = None,
        functions: FrozenDict[str, tuple[FunctionRule, ...]] | None = None,
    ) -> KoreDefn:
        return KoreDefn(
            sorts=self.sorts if sorts is None else sorts,
            symbols=self.symbols if symbols is None else symbols,
            subsorts=self.subsorts if subsorts is None else subsorts,
            rewrites=self.rewrites if rewrites is None else rewrites,
            functions=self.functions if functions is None else functions,
        )

    def filter_rewrites(self, labels: Iterable[str]) -> KoreDefn:
        """Keep only rewrite rules with certain labels in the definition."""
        should_keep = set(labels)
        return self.let(rewrites=tuple(rewrite for rewrite in self.rewrites if rewrite.label in should_keep))

    def project_to_symbols(self) -> KoreDefn:
        """Project definition to symbols present in the definition."""
        functions: FrozenDict[str, tuple[FunctionRule, ...]] = FrozenDict(
            (function, rules) for function, rules in self.functions.items() if function in self.symbols
        )

        _sorts: set[str] = set()
        _sorts.update(sort for symbol in self.symbols for sort in self._symbol_sorts(symbol))
        _sorts.update(sort for rules in functions.values() for rule in rules for sort in self._arg_subsorts(rule))
        sorts: FrozenDict[str, SortDecl] = FrozenDict(
            (sort, decl) for sort, decl in self.sorts.items() if sort in _sorts
        )

        subsorts: FrozenDict[str, frozenset[str]] = FrozenDict(
            (supersort, frozenset(subsort for subsort in subsorts if subsort in sorts))
            for supersort, subsorts in self.subsorts.items()
            if supersort in sorts
        )

        return self.let(
            sorts=sorts,
            subsorts=subsorts,
            functions=functions,
        )

    def project_to_rewrites(self) -> KoreDefn:
        """Project definition to symbols that are part of the configuration or are (transitively) referred to from rewrite axioms."""
        _symbols = set()
        _symbols.update(self._config_symbols())
        _symbols.update(self._rewrite_symbols())
        symbols: FrozenDict[str, SymbolDecl] = FrozenDict(
            (symbol, decl) for symbol, decl in self.symbols.items() if symbol in _symbols
        )
        return self.let(symbols=symbols).project_to_symbols()

    def _symbol_sorts(self, symbol: str) -> list[str]:
        decl = self.symbols[symbol]
        res = []
        if isinstance(decl.sort, SortApp):
            res.append(decl.sort.name)
        res.extend(sort.name for sort in decl.param_sorts if isinstance(sort, SortApp))
        return res

    def _arg_subsorts(self, rule: FunctionRule) -> set[str]:
        """Collect the from-sorts of injections on the LHS of a function rule.

        These potentially indicate matching on a subsort of a certain sort, e.g.
        rule isKResult(inj{KResult,KItem}(KResult)) => true
        """
        res = set()

        def from_sort(pattern: Pattern) -> None:
            match pattern:
                case App('inj', (SortApp(sort), _), _):
                    res.add(sort)

        rule.lhs.collect(from_sort)
        return res

    def _config_symbols(self) -> set[str]:
        """Return the set of symbols that constitute a configuration."""
        res: set[str] = set()
        done = set()
        pending = ['SortGeneratedTopCell']
        while pending:
            sort = pending.pop()
            if sort in done:
                continue
            done.add(sort)

            symbols: list[str] = []
            if sort in self.collections:
                coll = self.collections[sort]
                symbols += [coll.concat, coll.element, coll.unit]
            symbols += self.constructors.get(sort, ())

            pending.extend(sort for symbol in symbols for sort in self._symbol_sorts(symbol))
            res.update(symbols)
        return res

    def _rewrite_symbols(self) -> set[str]:
        """Return the set of symbols reffered to in rewrite rules."""
        res = set()

        # Symbols appearing in rewrite rules are relevant
        pending = {
            symbol for rewrite_rule in self.rewrites for symbol in collect_symbols(rewrite_rule.to_axiom().pattern)
        }
        while pending:
            symbol = pending.pop()
            if symbol in res:
                continue

            res.add(symbol)

            # Symbols appearing in function rules of a releveant symbol are relevant
            pending.update(
                symbol
                for function_rule in self.functions.get(symbol, ())
                for symbol in collect_symbols(function_rule.to_axiom().pattern)
            )

            # If the symbol consumes or produces a collection, collection function symbols are relevant
            for sort in self._symbol_sorts(symbol):
                if sort in self.collections:
                    coll = self.collections[sort]
                    pending.update([coll.concat, coll.element, coll.unit])

        return res
