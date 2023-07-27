from __future__ import annotations

import logging
from collections import defaultdict
from dataclasses import dataclass
from functools import cached_property, reduce
from pathlib import Path
from typing import TYPE_CHECKING, Final, final

from ..cli.utils import check_dir_path, check_file_path
from ..utils import FrozenDict
from .parser import KoreParser
from .syntax import App, SortApp

if TYPE_CHECKING:
    from collections.abc import Iterable

    from .syntax import Definition, Pattern, Sort

_LOGGER: Final = logging.getLogger(__name__)


@final
@dataclass(frozen=True)
class KompiledKore:
    path: Path
    timestamp: int

    def __init__(self, definition_dir: str | Path):
        definition_dir = Path(definition_dir)
        check_dir_path(definition_dir)

        path = (definition_dir / 'definition.kore').resolve()
        check_file_path(path)

        timestamp_file = definition_dir / 'timestamp'
        check_file_path(timestamp_file)
        timestamp = timestamp_file.stat().st_mtime_ns

        object.__setattr__(self, 'path', path)
        object.__setattr__(self, 'timestamp', timestamp)

    @cached_property
    def definition(self) -> Definition:
        _LOGGER.info(f'Loading kore definition: {self.path}')
        kore_text = self.path.read_text()
        _LOGGER.info(f'Parsing kore definition: {self.path}')
        return KoreParser(kore_text).definition()

    @cached_property
    def _subsort_table(self) -> FrozenDict[Sort, frozenset[Sort]]:
        axioms = (axiom for module in self.definition for axiom in module.axioms)
        attrs = (attr for axiom in axioms for attr in axiom.attrs)
        subsort_attrs = (attr for attr in attrs if attr.symbol == 'subsort')
        subsort_attr_sorts = (attr.sorts for attr in subsort_attrs)

        direct_subsorts: dict[Sort, set[Sort]] = defaultdict(set)
        for subsort, supersort in subsort_attr_sorts:
            direct_subsorts[supersort].add(subsort)

        supersorts = direct_subsorts.keys()

        subsort_table = dict(direct_subsorts)
        for sort_k in supersorts:
            for sort_j in supersorts:
                if sort_k not in subsort_table[sort_j]:
                    continue

                for sort_i in subsort_table[sort_k]:
                    subsort_table[sort_j].add(sort_i)

        return FrozenDict((supersort, frozenset(subsorts)) for supersort, subsorts in subsort_table.items())

    def is_subsort(self, sort1: Sort, sort2: Sort) -> bool:
        if sort1 == sort2:
            return True

        if sort2 == SortApp('SortK'):
            return True

        if sort1 == SortApp('SortK'):
            return False

        return sort1 in self._subsort_table.get(sort2, frozenset())

    def meet_sorts(self, sort1: Sort, sort2: Sort) -> Sort:
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

    def meet_all_sorts(self, sorts: Iterable[Sort]) -> Sort:
        unit: Sort = SortApp('SortK')
        return reduce(self.meet_sorts, sorts, unit)

    def add_injections(self, pattern: Pattern, sort: Sort | None = None) -> Pattern:
        if sort is None:
            sort = SortApp('SortK')
        patterns = pattern.patterns
        sorts = self.definition.pattern_sorts(pattern)
        pattern = pattern.let_patterns(self.add_injections(p, s) for p, s in zip(patterns, sorts, strict=True))
        return self._inject(pattern, sort)

    def _inject(self, pattern: Pattern, sort: Sort) -> Pattern:
        actual_sort = self.definition.infer_sort(pattern)

        if actual_sort == sort:
            return pattern

        if self.is_subsort(actual_sort, sort):
            return App('inj', (actual_sort, sort), (pattern,))

        raise ValueError(f'Sort {actual_sort.name} is not a subsort of {sort.name}: {pattern}')
