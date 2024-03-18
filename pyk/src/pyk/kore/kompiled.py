from __future__ import annotations

import json
import logging
from dataclasses import dataclass
from itertools import chain
from pathlib import Path
from typing import TYPE_CHECKING, Final, final

from ..utils import POSet, check_dir_path, check_file_path
from .parser import KoreParser
from .syntax import (
    DV,
    ML_SYMBOL_DECLS,
    App,
    MLPattern,
    MLQuant,
    Pattern,
    SortApp,
    SortVar,
    Symbol,
    SymbolDecl,
    WithSort,
)

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Any

    from ..utils import FrozenDict
    from .syntax import Definition, Kore, Sort

_LOGGER: Final = logging.getLogger(__name__)


_PYK_DEFINITION_NAME: Final = 'pyk-definition.kore.json'


@final
@dataclass(frozen=True)
class KompiledKore:
    sort_table: KoreSortTable
    symbol_table: KoreSymbolTable

    @staticmethod
    def load(definition_dir: str | Path) -> KompiledKore:
        definition_dir = Path(definition_dir)
        check_dir_path(definition_dir)

        kore_file = definition_dir / 'definition.kore'
        check_file_path(kore_file)

        json_file = definition_dir / _PYK_DEFINITION_NAME
        if json_file.exists():
            kore_timestamp = kore_file.stat().st_mtime_ns
            json_timestamp = json_file.stat().st_mtime_ns

            if kore_timestamp < json_timestamp:
                return KompiledKore.load_from_json(json_file)

            _LOGGER.warning(f'File is out of date: {json_file}')

        return KompiledKore.load_from_kore(kore_file)

    @staticmethod
    def load_from_kore(kore_file: str | Path) -> KompiledKore:
        kore_file = Path(kore_file)
        check_file_path(kore_file)

        _LOGGER.info(f'Reading KORE definition: {kore_file}')
        kore_text = kore_file.read_text()

        _LOGGER.info(f'Parsing KORE definition: {kore_file}')
        definition = KoreParser(kore_text).definition()

        return KompiledKore.for_definition(definition)

    @staticmethod
    def load_from_json(json_file: str | Path) -> KompiledKore:
        json_file = Path(json_file)
        check_file_path(json_file)
        _LOGGER.info(f'Reading JSON definition: {json_file}')
        with json_file.open() as f:
            json_data = json.load(f)
        return KompiledKore.from_dict(json_data)

    @staticmethod
    def for_definition(definition: Definition) -> KompiledKore:
        return KompiledKore(
            sort_table=KoreSortTable.for_definition(definition),
            symbol_table=KoreSymbolTable.for_definition(definition),
        )

    @staticmethod
    def from_dict(dct: dict[str, Any]) -> KompiledKore:
        return KompiledKore(
            sort_table=KoreSortTable(
                (_sort_from_dict(subsort), _sort_from_dict(supersort)) for subsort, supersort in dct['sorts']
            ),
            symbol_table=KoreSymbolTable(_symbol_decl_from_dict(symbol_decl) for symbol_decl in dct['symbols']),
        )

    def write(self, definition_dir: str | Path) -> None:
        definition_dir = Path(definition_dir)
        check_dir_path(definition_dir)
        json_data = self.to_dict()
        json_file = definition_dir / _PYK_DEFINITION_NAME
        with json_file.open('w') as f:
            json.dump(json_data, f)

    def to_dict(self) -> dict[str, Any]:
        return {
            'sorts': [
                [_to_dict(subsort), _to_dict(supersort)]
                for supersort, subsorts in self.sort_table._subsort_table.items()
                for subsort in subsorts
            ],
            'symbols': [_to_dict(symbol_decl) for symbol_decl in self.symbol_table._symbol_table.values()],
        }

    def add_injections(self, pattern: Pattern, sort: Sort | None = None) -> Pattern:
        if sort is None:
            sort = SortApp('SortK')

        stack: list = [pattern, sort, self.symbol_table.pattern_sorts(pattern), pattern.patterns, []]
        while True:
            done_patterns = stack[-1]
            patterns = stack[-2]
            pattern_sorts = stack[-3]
            _sort = stack[-4]
            pattern = stack[-5]

            idx = len(done_patterns) - len(patterns)
            if not idx:
                stack.pop()
                stack.pop()
                stack.pop()
                stack.pop()
                stack.pop()
                pattern = pattern.let_patterns(done_patterns)
                pattern = self._inject(pattern, _sort)
                if not stack:
                    return pattern
                stack[-1].append(pattern)
            else:
                pattern = patterns[idx]
                stack.append(pattern)
                stack.append(pattern_sorts[idx])
                stack.append(self.symbol_table.pattern_sorts(pattern))
                stack.append(pattern.patterns)
                stack.append([])

    def _inject(self, pattern: Pattern, sort: Sort) -> Pattern:
        actual_sort = self.symbol_table.infer_sort(pattern)

        if actual_sort == sort:
            return pattern

        if self.sort_table.is_subsort(actual_sort, sort):
            return App('inj', (actual_sort, sort), (pattern,))

        raise ValueError(f'Sort {actual_sort.name} is not a subsort of {sort.name}: {pattern}')


def _to_dict(kore: Kore) -> Any:
    match kore:
        case Pattern():
            return kore.dict
        case SortVar(name):
            return name
        case SortApp(name, sorts):
            return {'name': name, 'sorts': [_to_dict(sort) for sort in sorts]}
        case Symbol(name, vars):
            return {'name': name, 'vars': [_to_dict(var) for var in vars]}
        case SymbolDecl(symbol, param_sorts, sort, attrs, hooked):
            return {
                'symbol': _to_dict(symbol),
                'param-sorts': [_to_dict(sort) for sort in param_sorts],
                'sort': _to_dict(sort),
                'attrs': [_to_dict(attr) for attr in attrs],
                'hooked': hooked,
            }
        case _:
            raise AssertionError()


def _sort_from_dict(obj: Any) -> Sort:
    if isinstance(obj, str):
        return SortVar(obj)
    return SortApp(name=obj['name'], sorts=tuple(_to_dict(sort) for sort in obj['sorts']))


def _symbol_decl_from_dict(dct: Any) -> SymbolDecl:
    return SymbolDecl(
        symbol=Symbol(
            name=dct['symbol']['name'],
            vars=tuple(SortVar(var) for var in dct['symbol']['vars']),
        ),
        param_sorts=tuple(_sort_from_dict(sort) for sort in dct['param-sorts']),
        sort=_sort_from_dict(dct['sort']),
        attrs=tuple(_app_from_dict(attr) for attr in dct['attrs']),
        hooked=dct['hooked'],
    )


def _app_from_dict(dct: Any) -> App:
    app = Pattern.from_dict(dct)
    assert isinstance(app, App)
    return app


@final
@dataclass
class KoreSortTable:
    _subsort_table: FrozenDict[Sort, frozenset[Sort]]

    def __init__(self, subsorts: Iterable[tuple[Sort, Sort]]):
        poset = POSet((y, x) for x, y in subsorts)
        self._subsort_table = poset.image

    @staticmethod
    def for_definition(definition: Definition) -> KoreSortTable:
        axioms = (axiom for module in definition for axiom in module.axioms)
        attrs = (attr for axiom in axioms for attr in axiom.attrs)
        subsort_attrs = (attr for attr in attrs if attr.symbol == 'subsort')
        subsort_attr_sorts = (attr.sorts for attr in subsort_attrs)
        subsorts = ((subsort, supersort) for subsort, supersort in subsort_attr_sorts)
        return KoreSortTable(subsorts)

    def is_subsort(self, sort1: Sort, sort2: Sort) -> bool:
        if sort1 == sort2:
            return True

        if sort2 == SortApp('SortK'):
            return True

        if sort1 == SortApp('SortK'):
            return False

        return sort1 in self._subsort_table.get(sort2, ())

    def meet(self, sort1: Sort, sort2: Sort) -> Sort:
        if self.is_subsort(sort1, sort2):
            return sort1

        if self.is_subsort(sort2, sort1):
            return sort2

        subsorts1 = set(self._subsort_table.get(sort1, set())).union({sort1})
        subsorts2 = set(self._subsort_table.get(sort2, set())).union({sort2})
        common_subsorts = subsorts1.intersection(subsorts2)
        if not common_subsorts:
            raise ValueError(f'Sorts have no common subsort: {sort1}, {sort2}')
        nr_subsorts = {sort: len(self._subsort_table.get(sort, {})) for sort in common_subsorts}
        max_subsort_nr = max(n for _, n in nr_subsorts.items())
        max_subsorts = {sort for sort, n in nr_subsorts.items() if n == max_subsort_nr}
        (subsort,) = max_subsorts
        return subsort


@final
@dataclass
class KoreSymbolTable:
    _symbol_table: dict[str, SymbolDecl]

    def __init__(self, symbol_decls: Iterable[SymbolDecl] = ()):
        self._symbol_table = {symbol_decl.symbol.name: symbol_decl for symbol_decl in symbol_decls}

    @staticmethod
    def for_definition(definition: Definition, *, with_ml_symbols: bool = True) -> KoreSymbolTable:
        return KoreSymbolTable(
            chain(
                (symbol_decl for module in definition for symbol_decl in module.symbol_decls),
                ML_SYMBOL_DECLS if with_ml_symbols else (),
            )
        )

    def resolve(self, symbol_id: str, sorts: Iterable[Sort] = ()) -> tuple[Sort, tuple[Sort, ...]]:
        symbol_decl = self._symbol_table.get(symbol_id)
        if not symbol_decl:
            raise ValueError(f'Undeclared symbol: {symbol_id}')

        symbol = symbol_decl.symbol
        sorts = tuple(sorts)

        nr_sort_vars = len(symbol.vars)
        nr_sorts = len(sorts)
        if nr_sort_vars != nr_sorts:
            raise ValueError(f'Expected {nr_sort_vars} sort parameters, got {nr_sorts} for: {symbol_id}')

        sort_table: dict[Sort, Sort] = dict(zip(symbol.vars, sorts, strict=True))

        def resolve_sort(sort: Sort) -> Sort:
            if type(sort) is SortVar:
                return sort_table.get(sort, sort)
            return sort

        sort = resolve_sort(symbol_decl.sort)
        param_sorts = tuple(resolve_sort(sort) for sort in symbol_decl.param_sorts)

        return sort, param_sorts

    def infer_sort(self, pattern: Pattern) -> Sort:
        if isinstance(pattern, WithSort):
            return pattern.sort

        if type(pattern) is App:
            sort, _ = self.resolve(pattern.symbol, pattern.sorts)
            return sort

        raise ValueError(f'Cannot infer sort: {pattern}')

    def pattern_sorts(self, pattern: Pattern) -> tuple[Sort, ...]:
        sorts: tuple[Sort, ...]
        if isinstance(pattern, DV):
            sorts = ()

        elif isinstance(pattern, MLQuant):
            sorts = (pattern.sort,)

        elif isinstance(pattern, MLPattern):
            _, sorts = self.resolve(pattern.symbol(), pattern.sorts)

        elif isinstance(pattern, App):
            _, sorts = self.resolve(pattern.symbol, pattern.sorts)

        else:
            sorts = ()

        assert len(sorts) == len(pattern.patterns)
        return sorts
