from __future__ import annotations

from typing import TYPE_CHECKING

from .syntax import And, App, EVar, MLQuant, Top

if TYPE_CHECKING:
    from collections.abc import Collection, Mapping

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


def substitute_vars(pattern: Pattern, subst_map: Mapping[EVar, Pattern]) -> Pattern:
    """Substitute variables in a pattern using a bottom-up traversal.

    Args:
        pattern: The pattern containing variables to be substituted.
        subst_map: A mapping from variables to their replacement patterns.
    """

    def subst(pattern: Pattern) -> Pattern:
        match pattern:
            case EVar() as var:
                return subst_map.get(var, var)
            case _:
                return pattern

    return pattern.bottom_up(subst)


def elim_aliases(pattern: Pattern) -> Pattern:
    r"""Eliminate subpatterns of the form ``\and{S}(p, X : S)``.

    Both the ``\and`` and instances of ``X : S`` are replaced by the definition ``p``.
    """
    aliases = {}

    def inline_aliases(pattern: Pattern) -> Pattern:
        match pattern:
            case And(_, (p, EVar() as var)):
                aliases[var] = p
                return p
            case _:
                return pattern

    pattern = pattern.bottom_up(inline_aliases)
    pattern = substitute_vars(pattern, aliases)
    return pattern
