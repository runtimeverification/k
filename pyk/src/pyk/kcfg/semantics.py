from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ..cterm import CTerm


class KCFGSemantics(ABC):
    @abstractmethod
    def is_terminal(self, c: CTerm) -> bool: ...

    @abstractmethod
    def abstract_node(self, c: CTerm) -> CTerm: ...

    @abstractmethod
    def same_loop(self, c1: CTerm, c2: CTerm) -> bool: ...

    @abstractmethod
    def is_loop(self, c1: CTerm) -> bool: ...


class DefaultSemantics(KCFGSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        return False

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False

    def is_loop(self, c1: CTerm) -> bool:
        return False
