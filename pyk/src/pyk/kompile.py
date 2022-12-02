from collections import defaultdict
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import Dict, FrozenSet, Set, Union, final

from .cli_utils import check_dir_path, check_file_path
from .kore.parser import KoreParser
from .kore.syntax import Definition, Sort
from .utils import FrozenDict


@final
@dataclass(frozen=True)
class KompiledDefn:
    path: Path
    timestamp: int

    def __init__(self, definition_dir: Union[str, Path]):
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
        return KoreParser(self.path.read_text()).definition()

    @cached_property
    def _subsort_dict(self) -> FrozenDict[Sort, FrozenSet[Sort]]:
        subsort_dict = _subsort_dict(self.definition)
        return FrozenDict({supersort: frozenset(subsorts) for supersort, subsorts in subsort_dict.items()})

    # Strict subsort, i.e. not reflexive
    def _is_subsort(self, subsort: Sort, supersort: Sort) -> bool:
        return subsort in self._subsort_dict.get(supersort, set())


def _subsort_dict(definition: Definition) -> Dict[Sort, Set[Sort]]:
    axioms = (axiom for module in definition for axiom in module.axioms)
    attrs = (attr for axiom in axioms for attr in axiom.attrs)
    subsort_attrs = (attr for attr in attrs if attr.symbol == 'subsort')
    subsort_attr_sorts = (attr.sorts for attr in subsort_attrs)

    res: Dict[Sort, Set[Sort]] = defaultdict(set)
    for subsort, supersort in subsort_attr_sorts:
        res[supersort].add(subsort)

    return res
