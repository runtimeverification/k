from __future__ import annotations

from typing import TYPE_CHECKING

from ..kore.syntax import (
    ML_SYMBOLS,
    AliasDecl,
    App,
    Assoc,
    Axiom,
    Claim,
    Definition,
    EVar,
    Import,
    LeftAssoc,
    MLPattern,
    Module,
    RightAssoc,
    SortApp,
    SortDecl,
    SortVar,
    String,
    SVar,
    Symbol,
    SymbolDecl,
    VarPattern,
)
from . import ast as kllvm

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Any

    from ..kore.syntax import Pattern, Sentence, Sort


# -----------
# pyk -> llvm
# -----------


def definition_to_llvm(definition: Definition) -> kllvm.Definition:
    res = kllvm.Definition()
    for mod in definition.modules:
        res.add_module(module_to_llvm(mod))
    _add_attributes(res, definition.attrs)
    return res


def module_to_llvm(module: Module) -> kllvm.Module:
    res = kllvm.Module(module.name)
    for sentence in module.sentences:
        res.add_declaration(sentence_to_llvm(sentence))
    _add_attributes(res, module.attrs)
    return res


def sentence_to_llvm(sentence: Sentence) -> kllvm.Declaration:
    match sentence:
        case Import(mod_name, attrs):
            res = kllvm.ModuleImportDeclaration(mod_name)
            _add_attributes(res, attrs)
            return res
        case SortDecl(name, vars, attrs, hooked):
            res = kllvm.CompositeSortDeclaration(name, hooked)
            for var in vars:
                res.add_object_sort_variable(sort_to_llvm(var))
            _add_attributes(res, attrs)
            return res
        case SymbolDecl(symbol, param_sorts, sort, attrs, hooked):
            res = kllvm.SymbolDeclaration(symbol.name, hooked)
            for var in symbol.vars:
                res.add_object_sort_variable(sort_to_llvm(var))
            for param_sort in param_sorts:
                res.symbol.add_argument(sort_to_llvm(param_sort))
            res.symbol.add_sort(sort_to_llvm(sort))
            _add_attributes(res, attrs)
            return res
        case AliasDecl(alias, param_sorts, sort, left, right, attrs):
            res = kllvm.AliasDeclaration(alias.name)
            for var in alias.vars:
                res.add_object_sort_variable(sort_to_llvm(var))
            for param_sort in param_sorts:
                res.symbol.add_argument(sort_to_llvm(param_sort))
            res.symbol.add_sort(sort_to_llvm(sort))
            res.add_variables(_composite_pattern(left.symbol, left.sorts, left.args))
            res.add_pattern(pattern_to_llvm(right))
            _add_attributes(res, attrs)
            return res
        case Axiom(vars, pattern, attrs):
            res = kllvm.AxiomDeclaration(False)
            for var in vars:
                res.add_object_sort_variable(sort_to_llvm(var))
            res.add_pattern(pattern_to_llvm(pattern))
            _add_attributes(res, attrs)
            return res
        case Claim(vars, pattern, attrs):
            res = kllvm.AxiomDeclaration(True)
            for var in vars:
                res.add_object_sort_variable(sort_to_llvm(var))
            res.add_pattern(pattern_to_llvm(pattern))
            _add_attributes(res, attrs)
            return res
        case _:
            raise AssertionError()


def pattern_to_llvm(pattern: Pattern) -> kllvm.Pattern:
    match pattern:
        case String(value):
            return kllvm.StringPattern(value.encode('latin-1'))
        case VarPattern(name, sort):
            return kllvm.VariablePattern(name, sort_to_llvm(sort))
        case App(symbol, sorts, args):
            return _composite_pattern(symbol, sorts, args)
        case Assoc():
            return _composite_pattern(pattern.kore_symbol(), [], [pattern.app])
        case MLPattern():
            return _composite_pattern(pattern.symbol(), pattern.sorts, pattern.ctor_patterns)
        case _:
            raise AssertionError()


def sort_to_llvm(sort: Sort) -> kllvm.Sort:
    match sort:
        case SortVar(name):
            return kllvm.SortVariable(name)
        case SortApp(name, sorts):
            res = kllvm.CompositeSort(sort.name, kllvm.value_type(kllvm.SortCategory(0)))
            for subsort in sorts:
                res.add_argument(sort_to_llvm(subsort))
            return res
        case _:
            raise AssertionError()


def _add_attributes(term: Any, attrs: tuple[App, ...]) -> None:
    for attr in attrs:
        term.add_attribute(_composite_pattern(attr.symbol, attr.sorts, attr.args))


def _composite_pattern(symbol_id: str, sorts: Iterable, patterns: Iterable[Pattern]) -> kllvm.CompositePattern:
    symbol = kllvm.Symbol(symbol_id)
    for sort in sorts:
        symbol.add_formal_argument(sort_to_llvm(sort))
    res = kllvm.CompositePattern(symbol)
    for pattern in patterns:
        res.add_argument(pattern_to_llvm(pattern))
    return res


# -----------
# llvm -> pyk
# -----------


def llvm_to_definition(definition: kllvm.Definition) -> Definition:
    modules = (llvm_to_module(mod) for mod in definition.modules)
    attrs = _attrs(definition.attributes)
    return Definition(modules, attrs)


def llvm_to_module(module: kllvm.Module) -> Module:
    sentences = (llvm_to_sentence(decl) for decl in module.declarations)
    attrs = _attrs(module.attributes)
    return Module(module.name, sentences, attrs)


def llvm_to_sentence(decl: kllvm.Declaration) -> Sentence:
    attrs = _attrs(decl.attributes)
    vars = tuple(llvm_to_sort_var(var) for var in decl.object_sort_variables)
    match decl:
        case kllvm.ModuleImportDeclaration():  # type: ignore
            return Import(decl.module_name, attrs)
        case kllvm.CompositeSortDeclaration():  # type: ignore
            return SortDecl(decl.name, vars, attrs, hooked=decl.is_hooked)
        case kllvm.SymbolDeclaration():  # type: ignore
            llvm_to_symbol = decl.symbol
            symbol = Symbol(llvm_to_symbol.name, vars)
            param_sorts = (llvm_to_sort(sort) for sort in llvm_to_symbol.arguments)
            sort = llvm_to_sort(llvm_to_symbol.sort)
            return SymbolDecl(symbol, param_sorts, sort, attrs, hooked=decl.is_hooked)
        case kllvm.AliasDeclaration():  # type: ignore
            llvm_to_symbol = decl.symbol
            symbol = Symbol(llvm_to_symbol.name, vars)
            param_sorts = (llvm_to_sort(sort) for sort in llvm_to_symbol.arguments)
            sort = llvm_to_sort(llvm_to_symbol.sort)
            left = App(*_unpack_composite_pattern(decl.variables))
            right = llvm_to_pattern(decl.pattern)
            return AliasDecl(symbol, param_sorts, sort, left, right, attrs)
        case kllvm.AxiomDeclaration():  # type: ignore
            pattern = llvm_to_pattern(decl.pattern)
            if decl.is_claim:
                return Claim(vars, pattern, attrs)
            else:
                return Axiom(vars, pattern, attrs)
        case _:
            raise AssertionError()


def llvm_to_pattern(pattern: kllvm.Pattern) -> Pattern:
    match pattern:
        case kllvm.StringPattern():  # type: ignore
            return String(pattern.contents.decode('latin-1'))
        case kllvm.VariablePattern():  # type: ignore
            if pattern.name and pattern.name[0] == '@':
                return SVar(pattern.name, llvm_to_sort(pattern.sort))
            else:
                return EVar(pattern.name, llvm_to_sort(pattern.sort))
        case kllvm.CompositePattern():  # type: ignore
            symbol, sorts, patterns = _unpack_composite_pattern(pattern)
            if symbol in ML_SYMBOLS:
                return MLPattern.of(symbol, sorts, patterns)
            elif symbol in [r'\left-assoc', r'\right-assoc']:
                (app,) = patterns
                assert isinstance(app, App)
                assoc = LeftAssoc if symbol == r'\left-assoc' else RightAssoc
                return assoc(app.symbol, app.sorts, app.args)
            else:
                return App(symbol, sorts, patterns)
        case _:
            raise AssertionError()


def llvm_to_sort(sort: kllvm.Sort) -> Sort:
    match sort:
        case kllvm.SortVariable():  # type: ignore
            return SortVar(sort.name)
        case kllvm.CompositeSort():  # type: ignore
            return SortApp(sort.name, (llvm_to_sort(subsort) for subsort in sort.arguments))
        case _:
            raise AssertionError()


def llvm_to_sort_var(var: kllvm.SortVariable) -> SortVar:
    return SortVar(var.name)


def _attrs(attributes: dict[str, kllvm.CompositePattern]) -> tuple[App, ...]:
    return tuple(App(*_unpack_composite_pattern(attr)) for _, attr in attributes.items())


def _unpack_composite_pattern(pattern: kllvm.CompositePattern) -> tuple[str, tuple[Sort, ...], tuple[Pattern, ...]]:
    symbol = pattern.constructor.name
    sorts = tuple(llvm_to_sort(sort) for sort in pattern.constructor.formal_arguments)
    patterns = tuple(llvm_to_pattern(subpattern) for subpattern in pattern.arguments)
    return symbol, sorts, patterns
