from __future__ import annotations

import logging
from functools import reduce
from itertools import repeat
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

from ..kast import EMPTY_ATT, Atts, KInner
from ..kast.att import Format
from ..kast.inner import KApply, KRewrite, KSort
from ..kast.manip import extract_lhs, extract_rhs
from ..kast.outer import KDefinition, KNonTerminal, KProduction, KRegexTerminal, KRule, KSyntaxSort, KTerminal
from ..kore.prelude import inj
from ..kore.syntax import (
    And,
    App,
    Axiom,
    Bottom,
    Equals,
    EVar,
    Exists,
    Implies,
    Import,
    Module,
    Not,
    Or,
    SortApp,
    SortDecl,
    SortVar,
    String,
    Symbol,
    SymbolDecl,
    Top,
)
from ..prelude.k import K_ITEM, K
from ..utils import FrozenDict, intersperse
from ._kast_to_kore import _kast_to_kore
from ._utils import munge

if TYPE_CHECKING:
    from collections.abc import Callable, Container, Iterable, Mapping
    from typing import Any, Final

    from ..kast import AttKey, KAtt
    from ..kast.inner import KLabel
    from ..kast.outer import KFlatModule, KSentence
    from ..kore.syntax import Pattern, Sentence, Sort

_LOGGER: Final = logging.getLogger(__name__)


KORE_KEYWORDS: Final = {
    'alias',
    'axiom',
    'endmodule',
    'hooked-sort',
    'hooked-symbol',
    'module',
    'sort',
    'symbol',
}


BUILTIN_LABELS: Final = {
    '#Bottom',
    '#Top',
    '#Not',
    '#Or',
    '#And',
    '#Implies',
    '#Equals',
    '#Ceil',
    '#Floor',
    '#Exists',
    '#Forall',
    '#AG',
    'weakExistsFinally',
    'weakAlwaysFinally',
}


def module_to_kore(definition: KDefinition) -> Module:
    """Convert the main module of a kompiled KAST definition to KORE format."""

    module = simplified_module(definition)
    defn = KDefinition(module.name, (module,))  # for getting the sort lattice

    name = name_to_kore(module.name)
    attrs = atts_to_kore({key: value for key, value in module.att.items() if key != Atts.DIGEST})  # filter digest

    imports = [Import('K')]
    sort_decls = [
        sort_decl_to_kore(syntax_sort)
        for syntax_sort in module.syntax_sorts
        if syntax_sort.sort.name not in [K.name, K_ITEM.name]
    ]
    symbol_decls = [
        symbol_prod_to_kore(sentence)
        for sentence in module.sentences
        if isinstance(sentence, KProduction) and sentence.klabel and sentence.klabel.name not in BUILTIN_LABELS
    ]

    sentences: list[Sentence] = []
    sentences += imports
    sentences += sort_decls
    sentences += symbol_decls
    sentences += _subsort_axioms(module)
    sentences += _assoc_axioms(defn)
    sentences += _idem_axioms(module)
    sentences += _unit_axioms(module)
    sentences += _functional_axioms(module)
    sentences += _no_confusion_axioms(module)
    sentences += _no_junk_axioms(defn)

    return Module(name=name, sentences=sentences, attrs=attrs)


# TODO should this be used in _klabel_to_kore?
def name_to_kore(name: str) -> str:
    if name in KORE_KEYWORDS:
        return f"{name}'Kywd'"
    return munge(name)


def atts_to_kore(att: Mapping[AttKey, Any]) -> list[App]:
    res = [att_to_kore(key, value) for key, value in att.items()]
    res.sort(key=lambda app: app.symbol)
    return res


def att_to_kore(key: AttKey, value: Any) -> App:
    symbol = name_to_kore(key.name)

    if value is None:
        return App(symbol)

    parse_res = _parse_special_att_value(key, value)
    if parse_res is not None:
        sorts, args = parse_res
        return App(symbol, sorts, args)

    if isinstance(value, str):
        return App(symbol, (), (String(value),))

    if isinstance(value, (dict, FrozenDict)) and 'node' in value:
        if value['node'] == 'KSort':
            sort_name = name_to_kore(KSort.from_dict(value).name)  # 'Sort' is not prepended by ModuleToKORE
            return App(symbol, (), (String(sort_name),))

        # TODO Should be kast_to_kore, but we do not have a KompiledKore.
        # TODO We should be able to add injections based on info in KDefinition.
        pattern = _kast_to_kore(KInner.from_dict(value))
        if not isinstance(pattern, App):
            raise ValueError('Expected application as attribure, got: {pattern.text}')
        return App(symbol, (), (pattern,))

    raise ValueError(f'Attribute conversion is not implemented for: {key}: {value}')


def _parse_special_att_value(key: AttKey, value: Any) -> tuple[tuple[Sort, ...], tuple[Pattern, ...]] | None:
    if key == Atts.LOCATION:
        assert isinstance(value, tuple)
        assert len(value) == 4
        loc_str = ','.join(str(loc) for loc in value)
        return (), (String(f'Location({loc_str})'),)
    if key == Atts.SOURCE:
        assert isinstance(value, Path)
        return (), (String(f'Source({value})'),)
    if key == Atts.FORMAT:
        assert isinstance(value, Format)
        return (), (String(value.unparse()),)
    if key == Atts.ELEMENT:
        # TODO avoid special casing by pre-processing the attribute into a KApply
        # This should be handled by the frontend
        assert isinstance(value, str)
        return (), (App(_label_name(value)),)
    if key == Atts.UNIT:  # TODO same here
        assert isinstance(value, str)
        return (), (App(_label_name(value)),)
    return None


def sort_decl_to_kore(syntax_sort: KSyntaxSort) -> SortDecl:
    name = _sort_name(syntax_sort.sort.name)
    attrs = atts_to_kore(syntax_sort.att)
    hooked = Atts.HOOK in syntax_sort.att
    return SortDecl(name, (), attrs=attrs, hooked=hooked)


def sort_to_kore(sort: KSort, production: KProduction | None = None) -> Sort:
    if production and sort in production.params:
        return _sort_var(sort)
    return _sort_app(sort)


def _sort_app(sort: KSort) -> SortApp:
    return SortApp(_sort_name(sort.name))


def _sort_var(sort: KSort) -> SortVar:
    return SortVar(_sort_name(sort.name))


def _sort_name(name: str) -> str:
    return 'Sort' + name_to_kore(name)


def _label_name(name: str) -> str:
    return 'Lbl' + name_to_kore(name)


def symbol_prod_to_kore(production: KProduction) -> SymbolDecl:
    if not production.klabel:
        raise ValueError(f'Expected symbol production, got: {production}')

    symbol_name = _label_name(production.klabel.name)
    symbol_vars = tuple(_sort_var(sort) for sort in production.params)
    symbol = Symbol(symbol_name, symbol_vars)

    param_sorts = tuple(sort_to_kore(item.sort, production) for item in production.non_terminals)
    sort = sort_to_kore(production.sort, production)
    attrs = atts_to_kore(production.att)
    hooked = Atts.HOOK in production.att
    return SymbolDecl(
        symbol=symbol,
        param_sorts=param_sorts,
        sort=sort,
        attrs=attrs,
        hooked=hooked,
    )


def _subsort_axioms(module: KFlatModule) -> list[Axiom]:
    def extract_subsort(production: KProduction) -> tuple[KSort, KSort] | None:
        if len(production.items) != 1:
            return None

        item = production.items[0]
        if not isinstance(item, KNonTerminal):
            return None

        assert not production.klabel
        return item.sort, production.sort

    def subsort_axiom(subsort: Sort, supersort: Sort) -> Axiom:
        R = SortVar('R')  # noqa: N806
        Val = EVar('Val', supersort)  # noqa: N806
        return Axiom(
            (R,),
            Exists(
                R,
                Val,
                Equals(
                    supersort,
                    R,
                    Val,
                    inj(subsort, supersort, EVar('From', subsort)),
                ),
            ),
            attrs=(App('subsort', (subsort, supersort), ()),),
        )

    res: list[Axiom] = []
    for sentence in module.sentences:
        if not isinstance(sentence, KProduction):
            continue

        subsort_res = extract_subsort(sentence)
        if not subsort_res:
            continue

        subsort, supersort = subsort_res
        if supersort == K:
            continue

        res.append(subsort_axiom(subsort=sort_to_kore(subsort), supersort=sort_to_kore(supersort)))

    return res


def _assoc_axioms(defn: KDefinition) -> list[Axiom]:
    def assoc_axiom(production: KProduction) -> Axiom:
        assert production.klabel

        try:
            left, right = production.non_terminals
        except ValueError as err:
            raise ValueError(f'Illegal use of the assoc attribute on non-binary production: {production}') from err

        def check_prod_sort_is_subsort_of(sort: KSort) -> None:
            if production.sort == sort:
                return
            if production.sort in defn.subsorts(sort):
                return
            raise ValueError(
                f'Sort {production.sort.name} is not a subsort of sort {sort.name}, associative production is not well-sorted: {production}'
            )

        check_prod_sort_is_subsort_of(left.sort)
        check_prod_sort_is_subsort_of(right.sort)

        symbol = _label_name(production.klabel.name)
        sort_params = tuple(_sort_var(param) for param in production.klabel.params)
        sort = sort_to_kore(production.sort, production)
        R = SortVar('R')  # noqa: N806
        K1, K2, K3 = (EVar(name, sort) for name in ['K1', 'K2', 'K3'])  # noqa: N806

        def app(left: Pattern, right: Pattern) -> App:
            return App(symbol, sort_params, (left, right))

        return Axiom(
            (R,) + sort_params,
            Equals(
                sort,
                R,
                app(app(K1, K2), K3),
                app(K1, app(K2, K3)),
            ),
            attrs=(App('assoc'),),
        )

    assert len(defn.modules) == 1
    module = defn.modules[0]

    res: list[Axiom] = []
    for sentence in module.sentences:
        if not isinstance(sentence, KProduction):
            continue
        if not sentence.klabel:
            continue
        if sentence.klabel.name in BUILTIN_LABELS:
            continue
        if not Atts.ASSOC in sentence.att:
            continue

        res.append(assoc_axiom(sentence))
    return res


def _idem_axioms(module: KFlatModule) -> list[Axiom]:
    def idem_axiom(production: KProduction) -> Axiom:
        assert production.klabel

        try:
            left, right = production.non_terminals
        except ValueError as err:
            raise ValueError(f'Illegal use of the idem attribute on non-binary production: {production}') from err

        def check_is_prod_sort(sort: KSort) -> None:
            if sort == production.sort:
                return
            raise ValueError(
                f'Sort {sort.name} is not {production.sort.name}, idempotent production is not well-sorted: {production}'
            )

        check_is_prod_sort(left.sort)
        check_is_prod_sort(right.sort)

        symbol = _label_name(production.klabel.name)
        sort_params = tuple(_sort_var(param) for param in production.klabel.params)
        sort = sort_to_kore(production.sort, production)
        R = SortVar('R')  # noqa: N806
        K = EVar('K', sort)  # noqa: N806

        return Axiom(
            (R,) + sort_params,
            Equals(sort, R, App(symbol, sort_params, (K, K)), K),
            attrs=(App('idem'),),
        )

    res: list[Axiom] = []
    for sentence in module.sentences:
        if not isinstance(sentence, KProduction):
            continue
        if not sentence.klabel:
            continue
        if sentence.klabel.name in BUILTIN_LABELS:
            continue
        if not Atts.IDEM in sentence.att:
            continue
        res.append(idem_axiom(sentence))
    return res


def _unit_axioms(module: KFlatModule) -> list[Axiom]:
    def unit_axioms(production: KProduction) -> tuple[Axiom, Axiom]:
        assert production.klabel

        try:
            left, right = production.non_terminals
        except ValueError as err:
            raise ValueError(f'Illegal use of the unit attribute on non-binary production: {production}') from err

        def check_is_prod_sort(sort: KSort) -> None:
            if sort == production.sort:
                return
            raise ValueError(
                f'Sort {sort.name} is not {production.sort.name}, unit production is not well-sorted: {production}'
            )

        check_is_prod_sort(left.sort)
        check_is_prod_sort(right.sort)

        symbol = _label_name(production.klabel.name)
        sort_params = tuple(_sort_var(param) for param in production.klabel.params)
        sort = sort_to_kore(production.sort, production)
        unit = App(_label_name(production.att[Atts.UNIT]))
        R = SortVar('R')  # noqa: N806
        K = EVar('K', sort)  # noqa: N806

        left_unit = Axiom(
            (R,) + sort_params,
            Equals(sort, R, App(symbol, sort_params, (K, unit)), K),
            attrs=(App('unit'),),
        )
        right_unit = Axiom(
            (R,) + sort_params,
            Equals(sort, R, App(symbol, sort_params, (unit, K)), K),
            attrs=(App('unit'),),
        )
        return left_unit, right_unit

    res: list[Axiom] = []
    for sentence in module.sentences:
        if not isinstance(sentence, KProduction):
            continue
        if not sentence.klabel:
            continue
        if sentence.klabel.name in BUILTIN_LABELS:
            continue
        if not Atts.FUNCTION in sentence.att:
            continue
        if not Atts.UNIT in sentence.att:
            continue
        res.extend(unit_axioms(sentence))
    return res


def _functional_axioms(module: KFlatModule) -> list[Axiom]:
    def functional_axiom(production: KProduction) -> Axiom:
        assert production.klabel

        symbol = _label_name(production.klabel.name)
        sort_params = tuple(_sort_var(param) for param in production.klabel.params)
        sort = sort_to_kore(production.sort, production)
        R = SortVar('R')  # noqa: N806
        Val = EVar('Val', sort)  # noqa: N806
        param_sorts = tuple(sort_to_kore(item.sort, production) for item in production.non_terminals)
        params = tuple(EVar(f'K{i}', sort) for i, sort in enumerate(param_sorts))

        return Axiom(
            (R,) + sort_params,
            Exists(
                R,
                Val,
                Equals(sort, R, Val, App(symbol, sort_params, params)),
            ),
            attrs=(App('functional'),),
        )

    res: list[Axiom] = []
    for sentence in module.sentences:
        if not isinstance(sentence, KProduction):
            continue
        if not sentence.klabel:
            continue
        if sentence.klabel.name in BUILTIN_LABELS:
            continue
        if not Atts.FUNCTIONAL in sentence.att:
            continue
        res.append(functional_axiom(sentence))
    return res


def _no_confusion_axioms(module: KFlatModule) -> list[Axiom]:
    def axiom_for_same_constr(production: KProduction) -> Axiom:
        assert production.klabel

        symbol = _label_name(production.klabel.name)
        sort_params = tuple(_sort_var(param) for param in production.klabel.params)
        sort = sort_to_kore(production.sort, production)

        def app(args: Iterable[Pattern]) -> App:
            return App(symbol, sort_params, args)

        param_sorts = tuple(sort_to_kore(item.sort, production) for item in production.non_terminals)
        xs = tuple(EVar(f'X{i}', sort) for i, sort in enumerate(param_sorts))
        ys = tuple(EVar(f'Y{i}', sort) for i, sort in enumerate(param_sorts))

        return Axiom(
            sort_params,
            Implies(
                sort,
                And(sort, (app(xs), app(ys))),
                app(And(x.sort, (x, y)) for x, y in zip(xs, ys, strict=True)),
            ),
            attrs=(App('constructor'),),
        )

    def axiom_for_diff_constr(prod1: KProduction, prod2: KProduction) -> Axiom:
        assert prod1.klabel
        assert prod2.klabel
        assert prod1.sort == prod2.sort

        sort = sort_to_kore(prod1.sort, prod1)

        symbol1 = _label_name(prod1.klabel.name)
        sort_params1 = tuple(_sort_var(param) for param in prod1.klabel.params)
        param_sorts1 = tuple(sort_to_kore(item.sort, prod1) for item in prod1.non_terminals)
        xs = tuple(EVar(f'X{i}', sort) for i, sort in enumerate(param_sorts1))

        symbol2 = _label_name(prod2.klabel.name)
        sort_params2 = tuple(_sort_var(param) for param in prod2.klabel.params)
        param_sorts2 = tuple(sort_to_kore(item.sort, prod2) for item in prod2.non_terminals)
        ys = tuple(EVar(f'Y{i}', sort) for i, sort in enumerate(param_sorts2))

        return Axiom(
            sort_params1,  # TODO Why the asymmetry?
            Not(
                sort,
                And(
                    sort,
                    (
                        App(symbol1, sort_params1, xs),
                        App(symbol2, sort_params2, ys),
                    ),
                ),
            ),
            attrs=(App('constructor'),),
        )

    prods = [
        sent
        for sent in module.sentences
        if isinstance(sent, KProduction)
        and sent.klabel
        and sent.klabel.name not in BUILTIN_LABELS
        and Atts.CONSTRUCTOR in sent.att
    ]

    res: list[Axiom] = []
    res += (axiom_for_same_constr(p) for p in prods if p.non_terminals)
    res += (
        axiom_for_diff_constr(p1, p2)
        for p1 in prods
        for p2 in prods
        if p1.sort == p2.sort and p1.klabel and p2.klabel and p1.klabel.name < p2.klabel.name
    )
    return res


def _no_junk_axioms(defn: KDefinition) -> list[Axiom]:
    class NoJunk(NamedTuple):
        sort: KSort
        constructors: tuple[KProduction, ...]
        subsorts: tuple[KSort, ...]
        has_tokens: bool

        def axiom(self) -> Axiom | None:
            sort = sort_to_kore(self.sort)

            disjuncts: list[Pattern] = []
            disjuncts += (self.ctor_disjunct(prod) for prod in self.constructors)
            disjuncts += (self.subsort_disjunct(sort) for sort in self.subsorts)
            disjuncts += [Top(sort)] if self.has_tokens else []
            disjuncts += [Bottom(sort)]

            if len(disjuncts) == 1:
                return None

            return Axiom((), Or(sort, disjuncts), attrs=(App('constructor'),))

        def ctor_disjunct(self, production: KProduction) -> Pattern:
            assert production.klabel

            symbol = _label_name(production.klabel.name)
            sort_params = tuple(_sort_var(param) for param in production.klabel.params)
            sort = sort_to_kore(production.sort, production)
            param_sorts = tuple(sort_to_kore(item.sort, production) for item in production.non_terminals)
            params = tuple(EVar(f'X{i}', sort) for i, sort in enumerate(param_sorts))

            app: Pattern = App(symbol, sort_params, params)
            return reduce(lambda x, y: Exists(sort, y, x), reversed(params), app)

        def subsort_disjunct(self, subsort: KSort) -> Pattern:
            kore_sort = sort_to_kore(self.sort)
            kore_subsort = sort_to_kore(subsort)
            Val = EVar('Val', kore_subsort)  # noqa: N806
            return Exists(kore_sort, Val, inj(kore_subsort, kore_sort, Val))

    def no_junk_for(syntax_sort: KSyntaxSort, productions_for_sort: Iterable[KProduction]) -> NoJunk:
        sort = syntax_sort.sort
        subsorts = tuple(sorted(defn.subsorts(sort), key=lambda s: s.name)) if sort != K else ()
        has_tokens = Atts.HAS_DOMAIN_VALUES in syntax_sort.att

        def key(production: KProduction) -> str:
            assert production.klabel
            return production.klabel.name

        constructors = tuple(
            sorted(
                (
                    prod
                    for prod in productions_for_sort
                    if prod.klabel and prod.klabel not in BUILTIN_LABELS and Atts.FUNCTION not in prod.att
                ),
                key=key,
            )
        )

        return NoJunk(sort, constructors, subsorts, has_tokens)

    assert len(defn.modules) == 1
    module = defn.modules[0]

    def prods_by_sort() -> dict[KSort, list[KProduction]]:
        res: dict[KSort, list[KProduction]] = {}
        for prod in module.productions:
            res.setdefault(prod.sort, []).append(prod)
        return res

    res: list[Axiom] = []
    prods = prods_by_sort()
    for syntax_sort in module.syntax_sorts:
        no_junk = no_junk_for(syntax_sort, prods.get(syntax_sort.sort, []))
        axiom = no_junk.axiom()
        if axiom:
            res.append(axiom)
    return res


# ----------------------------------
# Module to KORE: KAST preprocessing
# ----------------------------------


HOOK_NAMESPACES: Final = {
    'BOOL',
    'BUFFER',
    'BYTES',
    'FFI',
    'FLOAT',
    'INT',
    'IO',
    'JSON',
    'KEQUAL',
    'KREFLECTION',
    'LIST',
    'MAP',
    'MINT',
    'RANGEMAP',
    'SET',
    'STRING',
    'SUBSTITUTION',
    'UNIFICATION',
}


COLLECTION_HOOKS: Final = {
    'SET.Set',
    'MAP.Map',
    'LIST.List',
    'RANGEMAP.RangeMap',
}


def simplified_module(definition: KDefinition, module_name: str | None = None) -> KFlatModule:
    """
    In ModuleToKORE.java, there are some implicit KAST-to-KAST kompilation
    steps hidden in the conversion. In particular, the kompiled KAST definition
    (compiled.json) is modular, whereas the kompiled definition
    (definition.kore) is flat.

    This function aims to factor out these hidden KAST-to-KAST kompilation
    steps so that our implementation of module_to_kore can be as simple as
    possible. Moreover, this has the potential to shed some light on how
    modules can be kompiled incrementally.

    This function is an approximation, i.e. there might be cases where it
    produces a different result to what would be expected based on kompile's
    output. These discrepancies should be analyzed and fixed.
    """
    module_name = module_name or definition.main_module_name
    module = _flatten_module(definition, module_name)  # TODO KORE supports imports, why is definition.kore flat?

    # sorts
    module = _add_syntax_sorts(module)
    module = _add_collection_atts(module)
    module = _add_domain_value_atts(module)

    # symbols
    module = _pull_up_rewrites(module)
    module = _discard_symbol_atts(
        module,
        {
            Atts.CELL,
            Atts.CELL_FRAGMENT,
            Atts.CELL_NAME,
            Atts.CELL_OPT_ABSENT,
            Atts.GROUP,
            Atts.IMPURE,
            Atts.INDEX,
            Atts.INITIALIZER,
            Atts.MAINCELL,
            Atts.PREDICATE,
            Atts.PREFER,
            Atts.PRIVATE,
            Atts.PRODUCTION,
            Atts.PROJECTION,
            Atts.SEQSTRICT,
            Atts.STRICT,
            Atts.USER_LIST,
        },
    )
    module = _discard_hook_atts(module)
    module = _discard_format_atts(module)
    module = _add_anywhere_atts(module)
    module = _add_symbol_atts(module, Atts.MACRO, _is_macro)
    module = _add_symbol_atts(module, Atts.FUNCTIONAL, _is_functional)
    module = _add_symbol_atts(module, Atts.INJECTIVE, _is_injective)
    module = _add_symbol_atts(module, Atts.CONSTRUCTOR, _is_constructor)
    module = _add_default_format_atts(module)
    module = _inline_terminals_in_format_atts(module)
    module = _add_colors_atts(module)
    module = _discard_symbol_atts(module, [Atts.COLOR])
    module = _add_terminals_atts(module)

    return module


def _flatten_module(definition: KDefinition, module_name: str) -> KFlatModule:
    """Return a flat module with all sentences included and without imports"""
    module = definition.module(module_name)
    sentences = _imported_sentences(definition, module_name)
    return module.let(sentences=sentences, imports=())


def _imported_sentences(definition: KDefinition, module_name: str) -> list[KSentence]:
    """Return all sentences from imported modules, including the module itself."""

    pending: list[str] = [module_name]
    imported: set[str] = set()

    res: list[KSentence] = []
    while pending:
        module_name = pending.pop()
        if module_name in imported:
            continue
        module = definition.module(module_name)
        res += module.sentences
        pending += (importt.name for importt in module.imports)
        imported.add(module_name)

    return res


def _add_syntax_sorts(module: KFlatModule) -> KFlatModule:
    """Return a module with explicit syntax declarations: each sort is declared with the union of its attributes."""
    sentences = [sentence for sentence in module if not isinstance(sentence, KSyntaxSort)]
    sentences += _syntax_sorts(module)
    return module.let(sentences=sentences)


def _syntax_sorts(module: KFlatModule) -> list[KSyntaxSort]:
    """Return a declaration for each sort in the module."""
    declarations: dict[KSort, KAtt] = {}

    def is_higher_order(production: KProduction) -> bool:
        # Example: syntax {Sort} Sort ::= Sort "#as" Sort
        return production.sort in production.params

    # Merge attributes from KSyntaxSort instances
    for syntax_sort in module.syntax_sorts:
        sort = syntax_sort.sort
        if sort not in declarations:
            declarations[sort] = syntax_sort.att
        else:
            assert declarations[sort].keys().isdisjoint(syntax_sort.att)
            declarations[sort] = declarations[sort].update(syntax_sort.att.entries())

    # Also consider production sorts
    for production in module.productions:
        if is_higher_order(production):
            continue

        sort = production.sort
        if sort not in declarations:
            declarations[sort] = EMPTY_ATT

    return [KSyntaxSort(sort, att=att) for sort, att in declarations.items()]


def _add_collection_atts(module: KFlatModule) -> KFlatModule:
    """Return a module where concat, element and unit attributes are added to collection sort declarations."""

    # Example: syntax Map ::= Map Map [..., klabel(_Map_), element(_|->_), unit(.Map), ...]
    concat_prods = {prod.sort: prod for prod in module.productions if Atts.ELEMENT in prod.att}

    assert all(
        Atts.UNIT in prod.att for _, prod in concat_prods.items()
    )  # TODO Could be saved with a different attribute structure: concat(Element, Unit)

    def update_att(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KSyntaxSort):
            return sentence

        syntax_sort: KSyntaxSort = sentence

        if syntax_sort.att.get(Atts.HOOK) not in COLLECTION_HOOKS:
            return syntax_sort

        prod_att = concat_prods[syntax_sort.sort].att

        return syntax_sort.let(
            att=syntax_sort.att.update(
                [
                    # TODO Here, the attriubte is stored as dict, but ultimately we should parse known attributes in KAtt.from_dict
                    Atts.CONCAT(KApply(prod_att[Atts.KLABEL]).to_dict()),
                    # TODO Here, we keep the format from the frontend so that the attributes on SyntaxSort and Production are of the same type.
                    Atts.ELEMENT(prod_att[Atts.ELEMENT]),
                    Atts.UNIT(prod_att[Atts.UNIT]),
                ]
            )
        )

    sentences = tuple(update_att(sent) for sent in module)
    return module.let(sentences=sentences)


def _add_domain_value_atts(module: KFlatModule) -> KFlatModule:
    """Return a module where attribute "hasDomainValues" is added to all sort declarations that apply.

    The requirement on a sort declaration is to either have the "token" attribute directly
    or on a corresponding production.
    """

    token_sorts = _token_sorts(module)

    def update_att(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KSyntaxSort):
            return sentence

        syntax_sort: KSyntaxSort = sentence

        if syntax_sort.sort not in token_sorts:
            return syntax_sort

        return syntax_sort.let(att=syntax_sort.att.update([Atts.HAS_DOMAIN_VALUES(None)]))

    sentences = tuple(update_att(sent) for sent in module)
    return module.let(sentences=sentences)


def _token_sorts(module: KFlatModule) -> set[KSort]:
    res: set[KSort] = set()

    # TODO "token" should be an attribute of only productions
    for syntax_sort in module.syntax_sorts:
        if Atts.TOKEN in syntax_sort.att:
            res.add(syntax_sort.sort)

    for production in module.productions:
        if Atts.TOKEN in production.att:
            res.add(production.sort)

    return res


def _pull_up_rewrites(module: KFlatModule) -> KFlatModule:
    """Ensure that each rule is of the form X => Y."""

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KRule):
            return sentence
        if isinstance(sentence.body, KRewrite):
            return sentence
        rewrite = KRewrite(
            lhs=extract_lhs(sentence.body),
            rhs=extract_rhs(sentence.body),
        )
        return sentence.let(body=rewrite)

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _add_anywhere_atts(module: KFlatModule) -> KFlatModule:
    """Add the anywhere attribute to all symbol productions that are overloads or have a corresponding anywhere rule."""

    rules = _rules_by_klabel(module)
    productions_by_klabel_att = _productions_by_klabel_att(module.productions)
    defn = KDefinition(module.name, (module,))  # for getting the sort lattice

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        klabel = sentence.klabel
        if any(Atts.ANYWHERE in rule.att for rule in rules.get(klabel, [])):
            return sentence.let(att=sentence.att.update([Atts.ANYWHERE(None)]))

        if Atts.KLABEL not in sentence.att:
            return sentence

        productions = productions_by_klabel_att.get(sentence.att[Atts.KLABEL], [])
        if any(_is_overloaded_by(defn, production, sentence) for production in productions):
            return sentence.let(att=sentence.att.update([Atts.ANYWHERE(None)]))

        return sentence

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _rules_by_klabel(module: KFlatModule) -> dict[KLabel, list[KRule]]:
    """Return a dict that maps a label l to the list of all rules l => X.

    If a label does not have a matching rule, it will be not contained in the dict.
    The function expects that all rules have a rewrite on top.
    """
    res: dict[KLabel, list[KRule]] = {}
    for rule in module.rules:
        assert isinstance(rule.body, KRewrite)
        if not isinstance(rule.body.lhs, KApply):
            continue
        label = rule.body.lhs.label
        res.setdefault(label, []).append(rule)
    return res


def _add_symbol_atts(module: KFlatModule, att: AttKey[None], pred: Callable[[KAtt], bool]) -> KFlatModule:
    """Add attribute to symbol productions based on a predicate predicate."""

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:  # filter for symbol productions
            return sentence

        if pred(sentence.att):
            return sentence.let(att=sentence.att.update([att(None)]))

        return sentence

    return module.let(sentences=tuple(update(sent) for sent in module))


def _is_macro(att: KAtt) -> bool:
    return any(key in att for key in [Atts.ALIAS, Atts.ALIAS_REC, Atts.MACRO, Atts.MACRO_REC])


def _is_functional(att: KAtt) -> bool:
    return Atts.FUNCTION not in att or Atts.TOTAL in att


def _is_injective(att: KAtt) -> bool:
    return not any(
        key in att
        for key in [
            Atts.FUNCTION,
            Atts.ASSOC,
            Atts.COMM,
            Atts.IDEM,
            Atts.UNIT,
        ]
    )


def _is_constructor(att: KAtt) -> bool:
    return not any(
        key in att
        for key in [
            Atts.FUNCTION,
            Atts.ASSOC,
            Atts.COMM,
            Atts.IDEM,
            Atts.UNIT,
            Atts.MACRO,
            Atts.ANYWHERE,
        ]
    )


def _discard_hook_atts(module: KFlatModule, *, hook_namespaces: Iterable[str] = ()) -> KFlatModule:
    """Remove hook attributes from symbol productions that are not built-in and not activated."""

    def is_active(hook: str) -> bool:
        namespaces = (*hook_namespaces, *HOOK_NAMESPACES)
        return hook.startswith(tuple(f'{namespace}.' for namespace in namespaces))

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        if not Atts.HOOK in sentence.att:
            return sentence

        hook = sentence.att[Atts.HOOK]
        if not is_active(hook):
            return sentence.let(att=sentence.att.discard([Atts.HOOK]))

        return sentence

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _discard_format_atts(module: KFlatModule) -> KFlatModule:
    """Remove format attributes from symbol productions with items other than terminals and non-terminals."""

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        if all(isinstance(item, (KTerminal, KNonTerminal)) for item in sentence.items):
            return sentence

        return sentence.let(att=sentence.att.discard([Atts.FORMAT]))

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _discard_symbol_atts(module: KFlatModule, atts: Container[AttKey]) -> KFlatModule:
    """Remove certain attributes from symbol productions."""

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        return sentence.let(att=sentence.att.discard(atts))

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _productions_by_klabel_att(productions: Iterable[KProduction]) -> dict[str, list[KProduction]]:
    res: dict[str, list[KProduction]] = {}
    for production in productions:
        if not production.klabel:
            continue
        if Atts.KLABEL not in production.att:
            continue
        res.setdefault(production.att[Atts.KLABEL], []).append(production)
    return res


def _is_overloaded_by(defn: KDefinition, prod1: KProduction, prod2: KProduction) -> bool:
    if not prod1.klabel:
        raise ValueError(f'Expected symbol production, got: {prod1}')
    if not prod2.klabel:
        raise ValueError(f'Expected symbol production, got: {prod2}')
    if Atts.KLABEL not in prod1.att:
        return False
    if Atts.KLABEL not in prod2.att:
        return False
    if prod1.att[Atts.KLABEL] != prod2.att[Atts.KLABEL]:
        return False
    arg_sorts1 = prod1.argument_sorts
    arg_sorts2 = prod2.argument_sorts
    if len(arg_sorts1) != len(arg_sorts2):
        return False
    if prod1.sort not in defn.subsorts(prod2.sort):
        return False
    if any(sort1 not in defn.subsorts(sort2) for sort1, sort2 in zip(arg_sorts1, arg_sorts2, strict=True)):
        return False
    return prod1 != prod2


def _add_default_format_atts(module: KFlatModule) -> KFlatModule:
    """Add a default format attribute value to each symbol profuction missing one."""

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        if Atts.FORMAT in sentence.att:
            return sentence

        return sentence.let(att=sentence.att.update([Atts.FORMAT(sentence.default_format)]))

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _inline_terminals_in_format_atts(module: KFlatModule) -> KFlatModule:
    """For a terminal `"foo"` change `%i` to `%cfoo%r`. For a non-terminal, decrease the index."""

    def inline_terminals(formatt: Format, production: KProduction) -> Format:
        nt_indexes: dict[int, int] = {}
        nt_index = 1
        for i, item in enumerate(production.items):
            if isinstance(item, KNonTerminal):
                nt_indexes[i] = nt_index
                nt_index += 1

        tokens: list[str] = []
        for token in formatt.tokens:
            if len(token) > 1 and token[0] == '%' and token[1].isdigit():
                index = int(token[1:])
                if index > len(production.items):  # Note: index is 1-based
                    raise ValueError(r'Format index out of bounds: {token}')
                item_index = index - 1
                item = production.items[item_index]

                match item:
                    case KTerminal(value):
                        escaped = value.replace('\\', r'\\').replace('$', r'\$')
                        interspersed = intersperse(escaped.split('%'), '%%')
                        new_tokens = [s for s in interspersed if s]
                        tokens += ['%c']
                        tokens += new_tokens
                        tokens += ['%r']
                    case KNonTerminal():
                        new_index = nt_indexes[item_index]
                        tokens.append(f'%{new_index}')
                    case _:
                        assert isinstance(item, KRegexTerminal)
                        raise ValueError(r'Invalid reference to regex terminal: {token}')
            else:
                tokens.append(token)
        return Format(tokens)

    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        if Atts.FORMAT not in sentence.att:
            return sentence

        formatt = sentence.att[Atts.FORMAT]
        formatt = inline_terminals(formatt, sentence)

        return sentence.let(att=sentence.att.update([Atts.FORMAT(formatt)]))

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _add_colors_atts(module: KFlatModule) -> KFlatModule:
    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        if Atts.FORMAT not in sentence.att:
            return sentence

        if Atts.COLOR not in sentence.att:
            return sentence

        formatt = sentence.att[Atts.FORMAT]
        ncolors = sum(1 for token in formatt.tokens if token == '%c')
        color = sentence.att[Atts.COLOR]
        colors = ','.join(repeat(color, ncolors))

        return sentence.let(att=sentence.att.update([Atts.COLORS(colors)]))

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)


def _add_terminals_atts(module: KFlatModule) -> KFlatModule:
    def update(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KProduction):
            return sentence

        if not sentence.klabel:
            return sentence

        terminals = ''.join('0' if isinstance(item, KNonTerminal) else '1' for item in sentence.items)
        return sentence.let(att=sentence.att.update([Atts.TERMINALS(terminals)]))

    sentences = tuple(update(sent) for sent in module)
    return module.let(sentences=sentences)
