from __future__ import annotations

import re
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property
from graphlib import TopologicalSorter
from itertools import count
from typing import TYPE_CHECKING, NamedTuple, TypedDict

import networkx as nx

from ..dequote import bytes_encode
from ..konvert import unmunge
from ..kore.internal import CollectionKind
from ..kore.kompiled import KoreSymbolTable
from ..kore.manip import collect_symbols, elim_aliases, free_occs
from ..kore.syntax import DV, And, App, EVar, SortApp, String, Top
from ..utils import FrozenDict, POSet
from .model import (
    Alt,
    AltsFieldVal,
    AltsVal,
    Axiom,
    Ctor,
    Definition,
    ExplBinder,
    ImplBinder,
    Inductive,
    Instance,
    InstField,
    Modifiers,
    Module,
    Mutual,
    Signature,
    SimpleFieldVal,
    SimpleVal,
    StructCtor,
    Structure,
    StructVal,
    Term,
)

if TYPE_CHECKING:
    from collections.abc import Collection, Iterable, Iterator, Mapping
    from typing import Final

    from ..kore.internal import KoreDefn
    from ..kore.rule import FunctionRule, RewriteRule, Rule
    from ..kore.syntax import Pattern, Sort, SymbolDecl
    from .model import Binder, Command, Declaration, DeclVal, FieldVal


_PRELUDE_SORTS: Final = {
    'SortBool',
    'SortBytes',
    'SortId',
    'SortInt',
    'SortString',
    'SortStringBuffer',
    'SortEndianness',
    'SortSignedness',
}
_PRELUDE_FUNCS: Final = {
    "Lbl'UndsPlus'Int'Unds'",  # +Int
    "Lbl'Unds'-Int'Unds'",  # -Int
    "Lbl'UndsStar'Int'Unds'",  # *Int
    "Lbl'UndsSlsh'Int'Unds'",  # /Int
    "Lbl'Unds'modInt'Unds'",  # modInt
    "Lbl'UndsXor-Perc'Int'UndsUnds'",  # ^%Int
    "LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int",  # maxInt
    "Lbl'Tild'Int'Unds'",  # ~Int
    "Lbl'Unds-LT-Eqls'Int'Unds'",  # <=Int
    "Lbl'Unds-GT-Eqls'Int'Unds'",  # >=Int
    "Lbl'Unds-LT-'Int'Unds'",  # <Int
    "Lbl'Unds-GT-'Int'Unds'",  # >Int
    "Lbl'UndsEqlsEqls'Int'Unds'",  # ==Int
    "Lbl'Stop'Bytes'Unds'BYTES-HOOKED'Unds'Bytes",  # Bytes.empty
    "Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int",  # Int.log2
    "LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Int'Unds'Endianness",  # Int2Bytes
    "LblBytes2Int'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Endianness'Unds'Signedness",  # Bytes2Int
    "LblpadRightBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int",  # padRight
    "LblpadLeftBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int",  # padLeft
    "LbllengthBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes",  # Bytes.length
    "LblreplaceAtBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Bytes",  # Bytes.replaceAt
    "LblsubstrBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int",  # Bytes.substr
}

_SYMBOL_OVERRIDES: Final = {
    'Lblite': 'kite',
    'Lblabs': 'kabs',
}


class Field(NamedTuple):
    name: str
    ty: Term


class Matcher(ABC):
    @cached_property
    def inputs(self) -> frozenset[EVar]:
        return frozenset(v for pat in self._input_patterns() for vs in free_occs(pat).values() for v in vs)

    @cached_property
    def outputs(self) -> frozenset[EVar]:
        return frozenset(v for pat in self._output_patterns() for vs in free_occs(pat).values() for v in vs)

    @abstractmethod
    def _input_patterns(self) -> list[Pattern]: ...

    @abstractmethod
    def _output_patterns(self) -> list[Pattern]: ...


@dataclass(frozen=True)
class EqMatcher(Matcher):
    var1: EVar
    var2: EVar

    def _input_patterns(self) -> list[Pattern]:
        return [self.var1, self.var2]

    def _output_patterns(self) -> list[Pattern]:
        return []


class BaseMatcher(Matcher, ABC):
    var: EVar

    def _input_patterns(self) -> list[Pattern]:
        return [self.var]

    def _output_patterns(self) -> list[Pattern]:
        return []


@dataclass(frozen=True)
class SubsortMatcher(BaseMatcher):
    var: EVar
    subsort: str
    supersort: str
    pattern: Pattern

    def _output_patterns(self) -> list[Pattern]:
        return [self.pattern]


@dataclass(frozen=True)
class ListMatcher(BaseMatcher):
    var: EVar
    prefix: tuple[Pattern, ...]
    middle: Pattern
    suffix: tuple[Pattern, ...]

    def _output_patterns(self) -> list[Pattern]:
        res: list[Pattern] = []
        res.extend(self.prefix)
        res.append(self.middle)
        res.extend(self.suffix)
        return res


@dataclass(frozen=True)
class EmptyListMatcher(BaseMatcher):
    var: EVar


@dataclass(frozen=True)
class SetMatcher(BaseMatcher):
    var: EVar
    elems: tuple[Pattern, ...]
    rest: Pattern

    def _input_patterns(self) -> list[Pattern]:
        res: list[Pattern] = []
        res.append(self.var)
        res.extend(self.elems)
        return res

    def _output_patterns(self) -> list[Pattern]:
        return [self.rest]


@dataclass(frozen=True)
class EmptySetMatcher(BaseMatcher):
    var: EVar


@dataclass(frozen=True)
class MapMatcher(BaseMatcher):
    var: EVar
    key_sort: str
    value_sort: str
    keys: tuple[Pattern, ...]
    values: tuple[Pattern, ...]
    rest: Pattern

    def _input_patterns(self) -> list[Pattern]:
        res: list[Pattern] = []
        res.append(self.var)
        res.extend(self.keys)
        return res

    def _output_patterns(self) -> list[Pattern]:
        res: list[Pattern] = []
        res.extend(self.values)
        res.append(self.rest)
        return res


@dataclass(frozen=True)
class EmptyMapMatcher(BaseMatcher):
    var: EVar
    key_sort: str
    value_sort: str


class Config(TypedDict, total=False):
    derive_beq: bool | None
    derive_decidableeq: bool | None


@dataclass
class K2Lean4:
    defn: KoreDefn
    derive_beq: bool
    derive_decidableeq: bool

    def __init__(self, defn: KoreDefn, *, config: Config | None = None):
        config = config or {}
        self.defn = defn
        self.derive_beq = bool(config.get('derive_beq'))
        self.derive_decidableeq = bool(config.get('derive_decidableeq'))

    @cached_property
    def symbol_table(self) -> KoreSymbolTable:
        return KoreSymbolTable(self.defn.symbols.values())

    @cached_property
    def structure_symbols(self) -> FrozenDict[str, str]:
        def constructed_by(symbol: str) -> str | None:
            decl = self.defn.symbols[symbol]
            _sort = decl.sort

            if not isinstance(_sort, SortApp):
                return None

            sort = _sort.name

            if not self._is_cell(sort) and not self._is_collection(sort):
                return None

            if symbol not in self.defn.constructors.get(sort, ()):
                return None

            return sort

        return FrozenDict(
            (symbol, sort) for symbol in self.defn.symbols if (sort := constructed_by(symbol)) is not None
        )

    @cached_property
    def structures(self) -> FrozenDict[str, tuple[Field, ...]]:
        def fields_of(sort: str) -> tuple[Field, ...] | None:
            if self._is_cell(sort):
                return self._cell_fields(sort)

            if self._is_collection(sort):
                return (self._collection_field(sort),)

            return None

        return FrozenDict((sort, fields) for sort in self.defn.sorts if (fields := fields_of(sort)) is not None)

    @cached_property
    def _sort_deps(self) -> FrozenDict[str, frozenset[str]]:
        """Transitively closed sort dependency graph."""
        sorts = self.defn.sorts
        deps: list[tuple[str, str]] = []
        for sort in sorts:
            # A sort depends on its subsorts (due to inj_{subsort} constructors)
            deps.extend((sort, subsort) for subsort in self.defn.subsorts.get(sort, []))
            # A sort depends on the parameter sorts of all its constructors
            deps.extend(
                (sort, param_sort)
                for ctor in self.defn.constructors.get(sort, [])
                for param_sort in _param_sorts(self.defn.symbols[ctor])
            )
            # If the sort is a collection, the element function parameters are dependencies
            if sort in self.defn.collections:
                coll = self.defn.collections[sort]
                elem = self.defn.symbols[coll.element]
                deps.extend((sort, param_sort) for param_sort in _param_sorts(elem))

        closed = POSet(deps).image  # TODO POSet should be called "transitively closed relation" or similar
        return FrozenDict(
            (sort, frozenset(closed.get(sort, []))) for sort in sorts
        )  # Ensure that sorts without dependencies are also represented

    @cached_property
    def _sort_sccs(self) -> tuple[tuple[str, ...], ...]:
        sccs = _ordered_sccs(self._sort_deps)
        return tuple(tuple(scc) for scc in sccs)

    @cached_property
    def _func_rules_by_uid(self) -> FrozenDict[str, FunctionRule]:
        return FrozenDict((rule.uid, rule) for rules in self.defn.functions.values() for rule in rules)

    @cached_property
    def _func_deps(self) -> FrozenDict[str, frozenset[str]]:
        deps: list[tuple[str, str]] = []
        elems: set[str] = set()
        for func, rules in self.defn.functions.items():
            elems.add(func)
            for rule in rules:
                elems.add(rule.uid)
                # A function depends on the rules that define it
                deps.append((func, rule.uid))
                # A rule depends on all the functions that it applies
                symbols = collect_symbols(
                    And(SortApp('SortFoo'), (rule.req or Top(SortApp('SortFoo')), *rule.lhs.args, rule.rhs))
                )  # Collection functions like `_List_` can occur on the LHS
                deps.extend((rule.uid, symbol) for symbol in symbols if symbol in self.defn.functions)

        closed = POSet(deps).image
        return FrozenDict((elem, frozenset(closed.get(elem, []))) for elem in elems)

    @cached_property
    def _func_sccs(self) -> tuple[tuple[str, ...], ...]:
        sccs = _ordered_sccs(self._func_deps)
        return tuple(tuple(scc) for scc in sccs)

    @cached_property
    def noncomputable(self) -> frozenset[str]:
        res: set[str] = set()

        for scc in self._func_sccs:
            assert scc
            elem = scc[0]

            if elem in self.defn.functions and elem not in _PRELUDE_FUNCS and not self.defn.functions[elem]:
                assert len(scc) == 1
                res.add(elem)

            if any(dep in res for dep in self._func_deps[elem]):
                res.update(scc)

        return frozenset(res)

    @staticmethod
    def _is_cell(sort: str) -> bool:
        return sort.endswith('Cell')

    def _cell_fields(self, sort: str) -> tuple[Field, ...]:
        (ctor,) = self.defn.constructors[sort]
        decl = self.defn.symbols[ctor]
        sorts = _param_sorts(decl)

        names: list[str]
        if all(self._is_cell(sort) for sort in sorts):
            names = []
            for sort in sorts:
                assert sort.startswith('Sort')
                assert sort.endswith('Cell')
                name = sort[4:-4]
                name = name[0].lower() + name[1:]
                names.append(name)
        else:
            assert len(sorts) == 1
            names = ['val']

        return tuple(Field(name, Term(sort)) for name, sort in zip(names, sorts, strict=True))

    def _is_collection(self, sort: str) -> bool:
        return sort in self.defn.collections

    def _collection_field(self, sort: str) -> Field:
        coll = self.defn.collections[sort]
        elem = self.defn.symbols[coll.element]
        sorts = _param_sorts(elem)
        term: Term
        match coll.kind:
            case CollectionKind.LIST:
                (item,) = sorts
                term = Term(f'List {item}')
            case CollectionKind.SET:
                (item,) = sorts
                term = Term(f'List {item}')
            case CollectionKind.MAP:
                key, value = sorts
                term = Term(f'List ({key} × {value})')
        return Field('coll', term)

    def sort_module(self) -> Module:
        commands: tuple[Command, ...] = tuple(
            block for sorts in self._sort_sccs if (block := self._sort_block(sorts)) is not None
        )
        return Module(commands=commands)

    def _sort_block(self, sorts: tuple[str, ...]) -> Command | None:
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
            return not decl.hooked and 'hasDomainValues' not in decl.attrs_by_key and not self._is_cell(sort)

        if is_inductive(sort):
            return self._inductive(sort)

        if sort in self.structures:
            return self._structure(sort)

        raise AssertionError

    def _inductive(self, sort: str) -> Inductive:
        subsorts = sorted(self.defn.subsorts.get(sort, ()))
        symbols = sorted(self.defn.constructors.get(sort, ()))
        ctors: list[Ctor] = []
        ctors.extend(self._inj_ctor(sort, subsort) for subsort in subsorts)
        ctors.extend(self._symbol_ctor(sort, symbol) for symbol in symbols)
        return Inductive(
            sort,
            Signature((), Term('Type')),
            ctors=ctors,
            deriving=self._deriving(sort),
        )

    def _inj_ctor(self, sort: str, subsort: str) -> Ctor:
        return Ctor(f'inj_{subsort}', Signature((ExplBinder(('x',), Term(subsort)),), Term(sort)))

    def _symbol_ctor(self, sort: str, symbol: str) -> Ctor:
        decl = self.defn.symbols[symbol]
        param_sorts = _param_sorts(decl)
        symbol = _symbol_ident(symbol)
        binders = tuple(ExplBinder((f'x{i}',), Term(sort)) for i, sort in enumerate(param_sorts))
        return Ctor(symbol, Signature(binders, Term(sort)))

    def _structure(self, sort: str) -> Structure:
        fields = self.structures[sort]
        binders = tuple(ExplBinder((name,), ty) for name, ty in fields)
        return Structure(
            sort,
            Signature((), Term('Type')),
            ctor=StructCtor(binders),
            deriving=self._deriving(sort),
        )

    def _deriving(self, sort: str) -> list[str]:
        res = []
        if self.derive_beq:
            res.append('BEq')
        if self.derive_decidableeq and not 'SortKItem' in self._sort_deps[sort]:
            res.append('DecidableEq')
        return res

    def inj_module(self) -> Module:
        return Module(commands=self._inj_commands())

    def _inj_commands(self) -> tuple[Command, ...]:
        return tuple(
            self._inj_instance(subsort, supersort)
            for supersort, subsorts in self.defn.subsorts.items()
            for subsort in subsorts
            if not supersort.endswith(
                'CellMap'
            )  # Strangely, cell collections can be injected from their value sort in KORE
        )

    def _inj_instance(self, subsort: str, supersort: str) -> Instance:
        ty = Term(f'Inj {subsort} {supersort}')
        fields = (
            self._inj_field(subsort, supersort),
            self._retr_field(subsort, supersort),
        )
        return Instance(Signature((), ty), StructVal(fields))

    def _inj_field(self, subsort: str, supersort: str) -> InstField:
        val = self._inj_val(subsort, supersort)
        return InstField('inj', val)

    def _inj_val(self, subsort: str, supersort: str) -> FieldVal:
        subsubsorts: list[str]
        if subsort.endswith('CellMap'):
            subsubsorts = []  # Disregard injection from value sort to cell map sort
        else:
            subsubsorts = sorted(self.defn.subsorts.get(subsort, []))

        if not subsubsorts:
            return SimpleFieldVal(Term(f'{supersort}.inj_{subsort}'))
        else:
            return AltsFieldVal(self._inj_alts(subsort, supersort, subsubsorts))

    def _inj_alts(self, subsort: str, supersort: str, subsubsorts: list[str]) -> list[Alt]:
        def inj(subsort: str, supersort: str, x: str) -> Term:
            return Term(f'{supersort}.inj_{subsort} {x}')

        res = []
        for subsubsort in subsubsorts:
            res.append(Alt((inj(subsubsort, subsort, 'x'),), inj(subsubsort, supersort, 'x')))

        if self.defn.constructors.get(subsort, []):
            # Has actual constructors, not only subsorts
            default = Alt((Term('x'),), inj(subsort, supersort, 'x'))
            res.append(default)

        return res

    def _retr_field(self, subsort: str, supersort: str) -> InstField:
        val = self._retr_val(subsort, supersort)
        return InstField('retr', val)

    def _retr_val(self, subsort: str, supersort: str) -> FieldVal:
        subsubsorts: list[str]
        if subsort.endswith('CellMap'):
            subsubsorts = []  # Disregard injection from value sort to cell map sort
        else:
            subsubsorts = sorted(self.defn.subsorts.get(subsort, []))

        return AltsFieldVal(self._retr_alts(subsort, supersort, subsubsorts))

    def _retr_alts(self, subsort: str, supersort: str, subsubsorts: list[str]) -> list[Alt]:
        def inj(subsort: str, supersort: str, x: str) -> Term:
            return Term(f'{supersort}.inj_{subsort} {x}')

        res = []
        for subsubsort in subsubsorts:
            res_inj = inj(subsubsort, subsort, 'x')
            res.append(Alt((inj(subsubsort, supersort, 'x'),), Term(f'some ({res_inj})')))

        res.append(Alt((inj(subsort, supersort, 'x'),), Term('some x')))

        n_covered = len(subsubsorts) + 1
        n_ctors = len(self.defn.constructors.get(supersort, ())) + len(self.defn.subsorts.get(supersort, ()))
        if n_ctors > n_covered:
            res.append(Alt((Term('_'),), Term('none')))

        return res

    def func_module(self) -> Module:
        sccs = self._func_sccs
        return Module(commands=tuple(command for elems in sccs if (command := self._func_block(elems))))

    def _func_block(self, elems: Iterable[str]) -> Command | None:
        assert elems
        elems = [elem for elem in elems if elem not in _PRELUDE_FUNCS]

        if not elems:
            return None

        if len(elems) == 1:
            (elem,) = elems
            return self._func_command(elem)

        return Mutual(commands=tuple(self._func_command(elem) for elem in elems))

    def _func_command(self, elem: str) -> Command:
        if elem in self.defn.functions:
            decl = self.defn.symbols[elem]
            rules = self.defn.functions[elem]
            if rules:
                return self._func_def(decl, rules)
            return self._func_axiom(decl)
        rule = self._func_rules_by_uid[elem]
        return self._func_rule_def(rule)

    def _func_def(self, decl: SymbolDecl, rules: tuple[FunctionRule, ...]) -> Definition:
        def sort_rules_by_priority(rules: tuple[FunctionRule, ...]) -> list[str]:
            grouped: dict[int, list[str]] = {}
            for rule in rules:
                grouped.setdefault(rule.priority, []).append(_rule_name(rule))
            groups = [sorted(grouped[priority]) for priority in sorted(grouped)]
            return [rule for group in groups for rule in group]

        assert rules

        sorted_rules = sort_rules_by_priority(rules)
        params = [f'x{i}' for i in range(len(decl.param_sorts))]
        arg_str = ' ' + ' '.join(params) if params else ''
        term: Term
        if len(sorted_rules) == 1:
            rule_str = sorted_rules[0]
            term = Term(f'{rule_str}{arg_str}')
        else:
            assert arg_str  # a function with multiple rules is not nullary
            rules_str = ' <|> '.join(f'({rule_str}{arg_str})' for rule_str in sorted_rules)
            term = Term(rules_str)

        val = SimpleVal(term)
        func = decl.symbol.name
        ident = _symbol_ident(func)
        signature = self._func_signature(decl)
        modifiers = Modifiers(noncomputable=True) if func in self.noncomputable else None

        return Definition(ident, val, signature, modifiers=modifiers)

    def _func_rule_def(self, rule: FunctionRule) -> Definition:
        decl = self.defn.symbols[rule.lhs.symbol]
        sort_params = [var.name for var in decl.symbol.vars]
        param_sorts = [sort.name for sort in decl.param_sorts]
        sort = decl.sort.name

        ident = _rule_name(rule)
        binders = (ImplBinder(sort_params, Term('Type')),) if sort_params else ()
        ty = Term(' → '.join(param_sorts + [f'Option {sort}']))
        modifiers = Modifiers(noncomputable=True) if rule.uid in self.noncomputable else None
        signature = Signature(binders, ty)

        req, lhs, rhs, defs = self._extract_func_rule(rule)
        free = (f"Var'Unds'Pat{i}" for i in count())
        args, matchers = self._func_rule_matchers(lhs, free)
        val = self._func_rule_val(args, matchers, req, rhs, defs)

        return Definition(ident, val, signature, modifiers=modifiers)

    def _extract_func_rule(self, rule: FunctionRule) -> tuple[Pattern, App, Pattern, dict[str, Pattern]]:
        req = rule.req if rule.req else Top(SortApp('Foo'))

        pattern = elim_aliases(And(SortApp('Foo'), (req, rule.lhs, rule.rhs)))
        assert isinstance(pattern, And)
        req, lhs, rhs = pattern.ops
        assert isinstance(lhs, App)

        free = (f"Var'Unds'Val{i}" for i in count())
        pattern, defs = self._elim_fun_apps(And(SortApp('Foo'), (req, rhs)), free)
        assert isinstance(pattern, And)
        req, rhs = pattern.ops

        return req, lhs, rhs, defs

    def _func_rule_val(
        self,
        args: list[Pattern],
        matchers: list[list[Matcher]],
        req: Pattern,
        rhs: Pattern,
        defs: dict[str, Pattern],
    ) -> DeclVal:
        rhs_term = self._func_rule_rhs(req, rhs, defs)
        term = self._func_rule_term(matchers, rhs_term)

        if not args:
            return SimpleVal(term)

        alts: list[Alt] = []

        match_alt = Alt(tuple(self._transform_pattern(arg, concrete=True) for arg in args), term)
        alts.append(match_alt)

        if not all(self._is_exhaustive(arg) for arg in args):
            nomatch_alt = Alt((Term('_'),) * len(args), Term('none'))
            alts.append(nomatch_alt)

        return AltsVal(alts)

    def _func_rule_term(self, matchers: list[list[Matcher]], rhs: Term) -> Term:
        def indent_rest(s: str, n: int) -> str:
            lines = s.splitlines()
            return '\n'.join([lines[0]] + [' ' * n + line for line in lines[1:]])

        match_groups = [
            list(zip(*(self._matcher_to_terms(matcher) for matcher in group), strict=True)) for group in matchers
        ]

        res = str(rhs)
        for group in reversed(match_groups):
            args_str = 'match {args} with\n'.format(args=', '.join(str(term) for term in group[0]))
            match_str = '  | {matches} => {res}\n'.format(
                matches=', '.join(str(term) for term in group[1]), res=indent_rest(res, 2)
            )
            nomatch_str = '  | {no_matches} => none'.format(no_matches=', '.join(['_'] * len(group[1])))
            res = f'{args_str}{match_str}{nomatch_str}'

        return Term(res)

    def _matcher_to_terms(self, matcher: Matcher) -> tuple[Term, Term]:
        def list_from(elems: Iterable[Pattern]) -> Term:
            elems_str = ', '.join(str(self._transform_pattern(elem, concrete=True)) for elem in elems)
            return Term(f'[{elems_str}]')

        match matcher:
            case EqMatcher(var1, var2):
                v1term = self._transform_pattern(var1)
                v2term = self._transform_pattern(var2)
                return Term(f'{v1term} == {v2term}'), Term('true')
            case SubsortMatcher(var, subsort, supersort, pat):
                vterm = self._transform_pattern(var)
                pterm = self._transform_arg(pat, concrete=True)
                return Term(f'(@retr {subsort} {supersort}) {vterm}'), Term(f'some {pterm}')
            case ListMatcher(var, prefix, middle, suffix):
                vterm = self._transform_pattern(var)
                arg = Term(f'(ListHook SortKItem).split {vterm}.coll {len(prefix)} {len(suffix)}')
                pterm = list_from(prefix)
                mterm = self._transform_pattern(middle, concrete=True)
                sterm = list_from(suffix)
                pattern = Term(f'some ({pterm}, {mterm}, {sterm})')
                return arg, pattern
            case EmptyListMatcher(var):
                vterm = self._transform_pattern(var)
                arg = Term(f'(ListHook SortKItem).size {vterm}.coll')
                pattern = Term('0')
                return arg, pattern
            case SetMatcher(var, elems, rest):
                vterm = self._transform_pattern(var)
                eterm = list_from(elems)
                rterm = self._transform_arg(rest, concrete=True)
                arg = Term(f'(SetHook SortKItem).split {vterm}.coll {eterm}')
                pattern = Term(f'some {rterm}')
                return arg, pattern
            case EmptySetMatcher(var):
                vterm = self._transform_pattern(var)
                arg = Term(f'(SetHook SortKItem).size {vterm}.coll')
                pattern = Term('0')
                return arg, pattern
            case MapMatcher(var, key_sort, value_sort, keys, values, rest):
                vterm = self._transform_pattern(var)
                kterm = list_from(keys)
                arg = Term(f'(MapHook {key_sort} {value_sort}).split {vterm}.coll {kterm}')
                vterm = list_from(values)
                rterm = self._transform_pattern(rest, concrete=True)
                pattern = Term(f'some ({vterm}, {rterm})')
                return arg, pattern
            case EmptyMapMatcher(var, key_sort, value_sort):
                vterm = self._transform_pattern(var)
                arg = Term(f'(MapHook {key_sort} {value_sort}).size {vterm}.coll')
                pattern = Term('0')
                return arg, pattern
            case _:
                raise AssertionError

    def _func_rule_rhs(self, req: Pattern, rhs: Pattern, defs: dict[str, Pattern]) -> Term:
        if not defs and isinstance(req, Top):
            return Term(f'some {self._transform_arg(rhs)}')

        seq_strs: list[str] = []
        seq_strs.extend(f'let {var} <- {self._transform_pattern(pattern)}' for var, pattern in defs.items())
        if not isinstance(req, Top):
            seq_strs.append(f'guard {self._transform_arg(req)}')
        seq_strs.append(f'return {self._transform_arg(rhs)}')
        do_str = '\n'.join('  ' + seq_str for seq_str in seq_strs)
        return Term(f'do\n{do_str}')

    def _is_exhaustive(self, pattern: Pattern) -> bool:
        match pattern:
            case DV():
                return False
            case EVar():
                return True
            case App(symbol, _, args) as app:
                if symbol in self.defn.functions:
                    # Collection function
                    return False

                _sort = self.symbol_table.infer_sort(app)
                assert isinstance(_sort, SortApp)
                sort = _sort.name
                n_ctors = len(self.defn.constructors.get(sort, ())) + len(self.defn.subsorts.get(sort, ()))
                assert n_ctors
                return n_ctors == 1 and all(self._is_exhaustive(arg) for arg in args)
            case _:
                raise AssertionError()

    def _func_rule_matchers(self, lhs: Pattern, free: Iterator[str]) -> tuple[list[Pattern], list[list[Matcher]]]:
        assert isinstance(lhs, App)  # pattern is the LHS of a function rule

        matchers: list[Matcher] = []

        def rename_outputs(pattern: Pattern, free: Iterator[str]) -> tuple[Pattern, dict[EVar, int]]:
            var_names = set(free_occs(pattern))
            class_idx = count()
            classes = {}

            def rename(pattern: Pattern) -> Pattern:
                match pattern:
                    case EVar() as var:
                        if var not in classes:
                            classes[var] = next(class_idx)
                            return pattern

                        while (new_name := next(free)) in var_names:
                            continue

                        var_names.add(new_name)
                        new_var = pattern.let(name=new_name)
                        classes[new_var] = classes[var]
                        return new_var
                    case App('LblSetItem'):
                        return pattern  # the arg is input
                    case App("Lbl'UndsPipe'-'-GT-Unds'", (), (key, value)):
                        return pattern.let(args=(key, rename(value)))  # the key is input
                    case App(symbol, (), (key, value)):
                        if symbol.endswith('CellMapItem'):
                            return pattern.let(args=(key, rename(value)))  # the key is input

                return pattern.let_patterns(tuple(rename(arg) for arg in pattern.patterns))

            return rename(pattern), classes

        def eq_matchers(classes: dict[EVar, int]) -> list[EqMatcher]:
            grouped: dict[int, list[EVar]] = {}
            for var, idx in classes.items():
                grouped.setdefault(idx, []).append(var)

            res = []
            for clazz in grouped.values():
                assert clazz
                representative, *rest = clazz
                for other in rest:
                    res.append(EqMatcher(representative, other))

            return res

        def abstract_matchers(pattern: Pattern) -> Pattern:
            match pattern:
                case App('inj', (SortApp(subsort), SortApp(supersort)), (pat,)):
                    if self.defn.subsorts.get(subsort) and free_occs(pat):
                        var = EVar(next(free), SortApp(supersort))
                        matchers.append(SubsortMatcher(var, subsort, supersort, pat))
                        return var
                case App("Lbl'Unds'List'Unds'", (), (App('LblListItem', (), (head,)), tail)):
                    var = EVar(next(free), SortApp('SortList'))
                    matchers.append(ListMatcher(var, (head,), tail, ()))
                    return var
                case App("Lbl'Unds'List'Unds'", (), (init, App('LblListItem', (), (last,)))):
                    var = EVar(next(free), SortApp('SortList'))
                    matchers.append(ListMatcher(var, (), init, (last,)))
                    return var
                case App("Lbl'Stop'List"):
                    var = EVar(next(free), SortApp('SortList'))
                    matchers.append(EmptyListMatcher(var))
                    return var
                case App("Lbl'Unds'Set'Unds'", (), (App('LblSetItem', (), (elem,)), rest)):
                    var = EVar(next(free), SortApp('SortSet'))
                    matchers.append(SetMatcher(var, (elem,), rest))
                    return var
                case App("Lbl'Stop'Set"):
                    var = EVar(next(free), SortApp('SortSet'))
                    matchers.append(EmptySetMatcher(var))
                    return var
                case App(map_symbol, (), (App(item_symbol, (), (key, value)), rest)):
                    if (
                        map_symbol.startswith("Lbl'Unds'")
                        and map_symbol.endswith("Map'Unds'")
                        and (
                            item_symbol == "Lbl'UndsPipe'-'-GT-Unds'"
                            or (item_symbol.startswith('Lbl') and item_symbol.endswith('CellMapItem'))
                        )
                    ):
                        sort = f'Sort{map_symbol[9:-6]}'
                        var = EVar(next(free), SortApp(sort))
                        coll = self.defn.collections[sort]
                        elem_decl = self.defn.symbols[coll.element]
                        key_sort, value_sort = _param_sorts(elem_decl)
                        matchers.append(MapMatcher(var, key_sort, value_sort, (key,), (value,), rest))
                        return var
                case App(symbol):
                    if symbol.startswith("Lbl'Stop'") and symbol.endswith('Map'):
                        sort = f'Sort{symbol[9:]}'
                        var = EVar(next(free), SortApp(sort))
                        coll = self.defn.collections[sort]
                        elem_decl = self.defn.symbols[coll.element]
                        key_sort, value_sort = _param_sorts(elem_decl)
                        matchers.append(EmptyMapMatcher(var, key_sort, value_sort))
                        return var

            return pattern

        def order_matchers(matchers: list[Matcher]) -> list[list[Matcher]]:
            prec: dict[int, list[int]] = {}
            for i, this in enumerate(matchers):
                prec[i] = []
                for j, other in enumerate(matchers):
                    if any(v in this.outputs for v in other.inputs):
                        prec[i].append(j)

            dg = nx.DiGraph(prec)
            generations = nx.topological_generations(dg)
            return [[matchers[i] for i in generation] for generation in generations]

        pattern, eq_classes = rename_outputs(lhs, (f"Var'Unds'Uniq{i}" for i in count()))
        matchers += eq_matchers(eq_classes)
        pattern = pattern.bottom_up(abstract_matchers)
        assert isinstance(pattern, App)
        ordered = order_matchers(matchers)

        return list(pattern.args), ordered

    def _func_axiom(self, decl: SymbolDecl) -> Axiom:
        ident = _symbol_ident(decl.symbol.name)
        signature = self._func_signature(decl)
        return Axiom(ident, signature)

    def _func_signature(self, decl: SymbolDecl) -> Signature:
        sort_params = [var.name for var in decl.symbol.vars]
        param_sorts = [sort.name for sort in decl.param_sorts]
        sort = decl.sort.name

        binders: list[Binder] = []
        if sort_params:
            binders.append(ImplBinder(sort_params, Term('Type')))
        binders.extend(ExplBinder((f'x{i}',), Term(sort)) for i, sort in enumerate(param_sorts))

        return Signature(binders, Term(f'Option {sort}'))

    def rewrite_module(self) -> Module:
        commands = (self._rewrite_inductive(),)
        return Module(commands=commands)

    def _rewrite_inductive(self) -> Inductive:
        def tran_ctor() -> Ctor:
            return Ctor(
                'tran',
                Signature(
                    (
                        ImplBinder(('s1', 's2', 's3'), Term('SortGeneratedTopCell')),
                        ExplBinder(('t1',), Term('Rewrites s1 s2')),
                        ExplBinder(('t2',), Term('Rewrites s2 s3')),
                    ),
                    Term('Rewrites s1 s3'),
                ),
            )

        ctors: list[Ctor] = []
        ctors.append(tran_ctor())
        ctors.extend(self._rewrite_ctors())
        signature = Signature(ty=Term('SortGeneratedTopCell → SortGeneratedTopCell → Prop'))
        return Inductive('Rewrites', signature, ctors=ctors)

    def _rewrite_ctors(self) -> list[Ctor]:
        rewrites = sorted(self.defn.rewrites, key=_rule_name)
        return [self._rewrite_ctor(rule) for rule in rewrites]

    def _rewrite_ctor(self, rule: RewriteRule) -> Ctor:
        req = rule.req if rule.req else Top(SortApp('Foo'))

        # Step 1: eliminate aliases
        pattern = elim_aliases(And(SortApp('Foo'), (req, rule.lhs, rule.rhs)))

        # Step 2: eliminate function application
        free = (f"Var'Unds'Val{i}" for i in count())
        pattern, defs = self._elim_fun_apps(pattern, free)

        # Step 3: create binders
        binders: list[Binder] = []
        binders.extend(
            self._free_binders(And(SortApp('Foo'), (pattern,) + tuple(defs.values())))
        )  # Binders of the form {x y : SortInt}
        binders.extend(self._def_binders(defs))  # Binders of the form (def_y : foo x = some y)

        # Step 4: transform patterns
        assert isinstance(pattern, And)
        req, lhs, rhs = pattern.ops

        if not isinstance(req, Top):
            req_term = self._transform_pattern(req)
            binders.append(ExplBinder(('req',), Term(f'{req_term} = true')))

        lhs_term = self._transform_pattern(lhs)
        rhs_term = self._transform_pattern(rhs)
        return Ctor(_rule_name(rule), Signature(binders, Term(f'Rewrites {lhs_term} {rhs_term}')))

    def _elim_fun_apps(self, pattern: Pattern, free: Iterator[str]) -> tuple[Pattern, dict[str, Pattern]]:
        """Replace ``foo(bar(x))`` with ``z`` and return mapping ``{y: bar(x), z: foo(y)}`` with ``y``, ``z`` fresh variables."""
        defs: dict[str, Pattern] = {}

        def abstract_funcs(pattern: Pattern) -> Pattern:
            if isinstance(pattern, App) and pattern.symbol in self.defn.functions:
                name = next(free)
                ident = _var_ident(name)
                defs[ident] = pattern
                sort = self.symbol_table.infer_sort(pattern)
                return EVar(name, sort)
            return pattern

        return pattern.bottom_up(abstract_funcs), defs

    def _free_binders(self, pattern: Pattern) -> list[Binder]:
        free_vars = {occ for _, occs in free_occs(pattern).items() for occ in occs}
        grouped_vars: dict[str, set[str]] = {}
        for var in free_vars:
            match var:
                case EVar(name, SortApp(sort)):
                    ident = _var_ident(name)
                    assert ident not in grouped_vars.get(sort, ())
                    grouped_vars.setdefault(sort, set()).add(ident)
                case _:
                    raise AssertionError()
        sorted_vars: dict[str, list[str]] = dict(
            sorted(((sort, sorted(idents)) for sort, idents in grouped_vars.items()), key=lambda item: item[1][0])
        )
        return [ImplBinder(idents, Term(sort)) for sort, idents in sorted_vars.items()]

    def _def_binders(self, defs: Mapping[str, Pattern]) -> list[Binder]:
        return [
            ExplBinder((f'defn{ident}',), Term(f'{self._transform_pattern(pattern)} = some {ident}'))
            for ident, pattern in defs.items()
        ]

    def _transform_pattern(self, pattern: Pattern, *, concrete: bool = False) -> Term:
        match pattern:
            case EVar(name):
                return self._transform_evar(name)
            case DV(SortApp(sort), String(value)):
                return self._transform_dv(sort, value)
            case App(symbol, sorts, args):
                return self._transform_app(symbol, sorts, args, concrete=concrete)
            case _:
                raise ValueError(f'Unsupported pattern: {pattern.text}')

    def _transform_arg(self, pattern: Pattern, *, concrete: bool = False) -> Term:
        term = self._transform_pattern(pattern, concrete=concrete)

        if not isinstance(pattern, App):
            return term

        if not pattern.args:
            return term

        if pattern.symbol in self.structure_symbols:
            return term

        return Term(f'({term})')

    def _transform_evar(self, name: str) -> Term:
        return Term(_var_ident(name))

    def _transform_dv(self, sort: str, value: str) -> Term:
        match sort:
            case 'SortBool':
                return Term(value)
            case 'SortInt':
                return self._transform_int_dv(value)
            case 'SortBytes':
                return self._transform_bytes_dv(value)
            case 'SortId' | 'SortString' | 'SortStringBuffer':
                return self._transform_string_dv(value)
            case _:
                raise ValueError(f'Unsupported sort: {sort}')

    def _transform_int_dv(self, value: str) -> Term:
        val = int(value)
        return Term(str(val)) if val >= 0 else Term(f'({val})')

    def _transform_bytes_dv(self, value: str) -> Term:
        bytes_str = ', '.join(f'0x{byte:02X}' for byte in bytes_encode(value))
        return Term(f'⟨#[{bytes_str}]⟩')

    def _transform_string_dv(self, value: str) -> Term:
        escapes = {
            ord('\r'): r'\r',
            ord('\n'): r'\n',
            ord('\t'): r'\t',
            ord('\\'): r'\\',
            ord('"'): r'\"',
            ord("'"): r"\'",
        }

        def encode(c: str) -> str:
            code = ord(c)
            if code in escapes:
                return escapes[code]
            elif 32 <= code < 127:
                return c
            elif code <= 0xFF:
                return fr'\x{code:02x}'
            elif code <= 0xFFFF:
                return fr'\u{code:04x}'
            else:
                raise ValueError(f"Unsupported character: '{c}' ({code})")

        encoded = ''.join(encode(c) for c in value)
        return Term(f'"{encoded}"')

    def _transform_app(
        self,
        symbol: str,
        sorts: tuple[Sort, ...],
        args: tuple[Pattern, ...],
        *,
        concrete: bool,
    ) -> Term:
        if symbol == 'inj':
            return self._transform_inj_app(sorts, args, concrete=concrete)

        if symbol in self.structure_symbols:
            fields = self.structures[self.structure_symbols[symbol]]
            return self._transform_structure_app(fields, args, concrete=concrete)

        decl = self.defn.symbols[symbol]
        sort = decl.sort.name if isinstance(decl.sort, SortApp) else None
        return self._transform_basic_app(sort, symbol, args, concrete=concrete)

    def _transform_inj_app(self, sorts: tuple[Sort, ...], args: tuple[Pattern, ...], *, concrete: bool) -> Term:
        _from_sort, _to_sort = sorts
        assert isinstance(_from_sort, SortApp)
        assert isinstance(_to_sort, SortApp)
        from_str = _from_sort.name
        to_str = _to_sort.name
        (arg,) = args
        term = self._transform_arg(arg, concrete=concrete)
        if concrete:
            return Term(f'{to_str}.inj_{from_str} {term}')
        else:
            return Term(f'(@inj {from_str} {to_str}) {term}')

    def _transform_structure_app(self, fields: Iterable[Field], args: Iterable[Pattern], *, concrete: bool) -> Term:
        fields_str = ', '.join(
            f'{field.name} := {self._transform_pattern(arg, concrete=concrete)}'
            for field, arg in zip(fields, args, strict=True)
        )
        lbrace, rbrace = ['{', '}']
        return Term(f'{lbrace} {fields_str} {rbrace}')

    def _transform_basic_app(self, sort: str | None, symbol: str, args: Iterable[Pattern], *, concrete: bool) -> Term:
        chunks = []

        ident: str
        if sort and symbol in self.defn.constructors.get(sort, ()):
            # Symbol is a constructor
            ident = f'{sort}.{_symbol_ident(symbol)}'
        else:
            ident = _symbol_ident(symbol)

        chunks.append(ident)
        chunks.extend(str(self._transform_arg(arg, concrete=concrete)) for arg in args)
        return Term(' '.join(chunks))


def _rule_name(rule: Rule) -> str:
    if rule.label:
        label = rule.label.replace('-', '_').replace('.', '_')
        return _escape_ident(label)
    return f'_{rule.uid[:7]}'


def _symbol_ident(symbol: str) -> str:
    if symbol in _SYMBOL_OVERRIDES:
        return _SYMBOL_OVERRIDES[symbol]
    if symbol.startswith('Lbl'):
        symbol = symbol[3:]
    return _escape_ident(symbol, kore=True)


def _var_ident(var: str) -> str:
    assert var.startswith('Var')
    return _escape_ident(var[3:], kore=True)


_VALID_LEAN_IDENT: Final = re.compile(
    "_[a-zA-Z0-9_?!']+|[a-zA-Z][a-zA-Z0-9_?!']*"
)  # Simplified to characters permitted in KORE in the first place


def _escape_ident(ident: str, *, kore: bool = False) -> str:
    if kore:
        ident = unmunge(ident)
    if not _VALID_LEAN_IDENT.fullmatch(ident):
        ident = f'«{ident}»'
    return ident


def _param_sorts(decl: SymbolDecl) -> list[str]:
    from ..utils import check_type

    return [check_type(sort, SortApp).name for sort in decl.param_sorts]  # TODO eliminate check_type


def _ordered_sccs(deps: Mapping[str, Collection[str]]) -> list[list[str]]:
    sccs = _sccs(deps)

    elems_by_scc: dict[int, set[str]] = {}
    for elem, scc in sccs.items():
        elems_by_scc.setdefault(scc, set()).add(elem)

    scc_deps: dict[int, set[int]] = {}
    for scc, elems in elems_by_scc.items():
        assert elems
        elem, *_ = elems
        scc_deps[scc] = set()
        for dep in deps[elem]:
            dep_scc = sccs[dep]
            if dep_scc == scc:
                continue
            scc_deps[scc].add(dep_scc)

    ordered_sccs = list(TopologicalSorter(scc_deps).static_order())
    return [sorted(elems_by_scc[scc]) for scc in ordered_sccs]


# TODO Implement a more efficient algorithm, e.g. Tarjan's algorithm
def _sccs(deps: Mapping[str, Iterable[str]]) -> dict[str, int]:
    res: dict[str, int] = {}

    scc = count()
    for elem, dep_elems in deps.items():
        if elem in res:
            continue
        idx = next(scc)
        res[elem] = idx
        for dep in dep_elems:
            if elem in deps[dep]:
                res[dep] = idx

    return res
