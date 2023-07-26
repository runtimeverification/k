from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ..cterm import CTerm
    from ..kast.inner import KInner


class KCFGSemantics(ABC):
    @abstractmethod
    def is_terminal(self, c: CTerm) -> bool:
        ...

    @abstractmethod
    def extract_branches(self, c: CTerm) -> list[KInner]:
        ...

    @abstractmethod
    def abstract_node(self, c: CTerm) -> CTerm:
        ...

    @abstractmethod
    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        ...


class DefaultSemantics(KCFGSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        return False

    def extract_branches(self, c: CTerm) -> list[KInner]:
        return []

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False
