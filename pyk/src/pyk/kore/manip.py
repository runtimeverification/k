from __future__ import annotations

from typing import TYPE_CHECKING

from .syntax import And, App, EVar, MLQuant, Top

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


def collect_symbols(pattern: Pattern) -> set[str]:
    """Return the set of all symbols referred to in a pattern.

    Args:
        pattern: Pattern to collect symbols from.
    """
    res: set[str] = set()

    def add_symbol(pattern: Pattern) -> None:
        match pattern:
            case App(symbol):
                res.add(symbol)

    pattern.collect(add_symbol)
    return res


def elim_aliases(pattern: Pattern) -> Pattern:
    r"""Eliminate subpatterns of the form ``\and{S}(p, X : S)``.

    Both the ``\and`` and instances of ``X : S`` are replaced by the definition ``p``.
    """
    aliases = {}

    def inline_aliases(pattern: Pattern) -> Pattern:
        match pattern:
            case And(_, (p, EVar(name))):
                aliases[name] = p
                return p
            case _:
                return pattern

    def substitute_vars(pattern: Pattern) -> Pattern:
        match pattern:
            case EVar(name) as var:
                return aliases.get(name, var)
            case _:
                return pattern

    pattern = pattern.bottom_up(inline_aliases)
    pattern = pattern.bottom_up(substitute_vars)
    return pattern
