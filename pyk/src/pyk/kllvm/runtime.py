from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from types import ModuleType
    from typing import Any

    from .ast import Pattern, Sort


class Runtime:
    _module: ModuleType

    def __init__(self, module: ModuleType):
        self._module = module

    def term(self, pattern: Pattern) -> Term:
        return Term(self._module.InternalTerm(pattern))

    def deserialize(self, bs: bytes) -> Term | None:
        block = self._module.InternalTerm.deserialize(bs)
        if block is None:
            return None
        return Term(block)

    def step(self, pattern: Pattern, depth: int | None = 1) -> Pattern:
        term = self.term(pattern)
        term.step(depth=depth)
        return term.pattern

    def run(self, pattern: Pattern) -> Pattern:
        return self.step(pattern, depth=None)

    def simplify(self, pattern: Pattern, sort: Sort) -> Pattern:
        return self._module.simplify_pattern(pattern, sort)

    def simplify_bool(self, pattern: Pattern) -> bool:
        return self._module.simplify_bool_pattern(pattern)


class Term:
    _block: Any  # module.InternalTerm

    def __init__(self, block: Any):
        self._block = block

    @property
    def pattern(self) -> Pattern:
        return self._block.to_pattern()

    def serialize(self) -> bytes:
        return self._block.serialize()

    def step(self, depth: int | None = 1) -> None:
        self._block = self._block.step(depth if depth is not None else -1)

    def run(self) -> None:
        self.step(depth=None)

    def __str__(self) -> str:
        return str(self._block)
