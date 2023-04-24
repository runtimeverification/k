from __future__ import annotations

from typing import TYPE_CHECKING

from ..kore.syntax import ML_SYMBOLS, App, EVar, MLPattern, SortApp, SortVar, String, SVar, VarPattern
from . import ast as kllvm

if TYPE_CHECKING:
    from collections.abc import Iterable

    from ..kore.syntax import Pattern, Sort


# -----------
# pyk -> llvm
# -----------


def kore_to_llvm(pattern: Pattern) -> kllvm.Pattern:
    match pattern:
        case String(value):
            return kllvm.StringPattern(value)
        case VarPattern(name, sort):
            return kllvm.VariablePattern(name, sort_to_llvm(sort))
        case App(symbol, sorts, args):
            return _composite_pattern(symbol, sorts, args)
        case MLPattern():
            return _composite_pattern(pattern.symbol(), pattern.sorts, pattern.ctor_patterns)
        case _:
            raise AssertionError()


def sort_to_llvm(sort: Sort) -> kllvm.Sort:
    match sort:
        case SortVar(name):
            return kllvm.SortVariable(name)
        case SortApp(name, sorts):
            res = kllvm.CompositeSort(sort.name, kllvm.ValueType(kllvm.SortCategory(0)))
            for subsort in sorts:
                res.add_argument(sort_to_llvm(subsort))
            return res
        case _:
            raise AssertionError()


def _composite_pattern(symbol_id: str, sorts: Iterable, patterns: Iterable[Pattern]) -> kllvm.CompositePattern:
    symbol = kllvm.Symbol(symbol_id)
    for sort in sorts:
        symbol.add_formal_argument(sort_to_llvm(sort))
    res = kllvm.CompositePattern(symbol)
    for pattern in patterns:
        res.add_argument(kore_to_llvm(pattern))
    return res


# -----------
# llvm -> pyk
# -----------


def llvm_to_kore(pattern: kllvm.Pattern) -> Pattern:
    match pattern:
        case kllvm.StringPattern():  # type: ignore
            return String(pattern.contents)
        case kllvm.VariablePattern():  # type: ignore
            if pattern.name and pattern.name[0] == '@':
                return SVar(pattern.name, llvm_to_sort(pattern.sort))
            else:
                return EVar(pattern.name, llvm_to_sort(pattern.sort))
        case kllvm.CompositePattern():  # type: ignore
            symbol = pattern.constructor.name
            sorts = (llvm_to_sort(sort) for sort in pattern.constructor.formal_arguments)
            patterns = (llvm_to_kore(subpattern) for subpattern in pattern.arguments)
            if symbol in ML_SYMBOLS:
                return MLPattern.of(symbol, sorts, patterns)
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
