from __future__ import annotations

from typing import TYPE_CHECKING

from .syntax import And, EVar, MLQuant, Top

if TYPE_CHECKING:
    from collections.abc import Collection

    from .syntax import Pattern


def conjuncts(pattern: Pattern) -> tuple[Pattern, ...]:
    if isinstance(pattern, Top):
        return ()
    if isinstance(pattern, And):
        return tuple(conjunct for op in pattern.ops for conjunct in conjuncts(op))
    return (pattern,)


def free_occs(pattern: Pattern, *, bound_vars: Collection[str] = ()) -> dict[str, list[EVar]]:
    occurrences: dict[str, list[EVar]] = {}

    def collect(pattern: Pattern, bound_vars: set[str]) -> None:
        if type(pattern) is EVar and pattern.name not in bound_vars:
            if pattern.name in occurrences:
                occurrences[pattern.name].append(pattern)
            else:
                occurrences[pattern.name] = [pattern]

        elif isinstance(pattern, MLQuant):
            new_bound_vars = {pattern.var.name}.union(bound_vars)
            collect(pattern.pattern, new_bound_vars)

        else:
            for sub_pattern in pattern.patterns:
                collect(sub_pattern, bound_vars)

    collect(pattern, set(bound_vars))
    return occurrences
