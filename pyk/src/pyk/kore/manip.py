from __future__ import annotations

from typing import TYPE_CHECKING

from .syntax import Assoc, EVar, MLQuant

if TYPE_CHECKING:
    from typing import Collection, Dict, List, Set

    from .syntax import Pattern


def free_occs(pattern: Pattern, *, bound_vars: Collection[str] = ()) -> Dict[str, List[EVar]]:
    occurrences: Dict[str, List[EVar]] = {}

    def collect(pattern: Pattern, bound_vars: Set[str]) -> None:
        if type(pattern) is EVar and pattern.name not in bound_vars:
            if pattern.name in occurrences:
                occurrences[pattern.name].append(pattern)
            else:
                occurrences[pattern.name] = [pattern]

        elif isinstance(pattern, Assoc):
            collect(pattern.app, bound_vars)

        elif isinstance(pattern, MLQuant):
            new_bound_vars = {pattern.var.name}.union(bound_vars)
            collect(pattern.pattern, new_bound_vars)

        else:
            for sub_pattern in pattern.patterns:
                collect(sub_pattern, bound_vars)

    collect(pattern, set(bound_vars))
    return occurrences
