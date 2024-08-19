from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ..cterm import CTerm
    from .kcfg import KCFGExtendResult


class KCFGSemantics(ABC):
    @abstractmethod
    def is_terminal(self, c: CTerm) -> bool: ...

    """Check whether or not a given ``CTerm`` is terminal."""

    @abstractmethod
    def abstract_node(self, c: CTerm) -> CTerm: ...

    """Implement an abstraction mechanism."""

    @abstractmethod
    def same_loop(self, c1: CTerm, c2: CTerm) -> bool: ...

    """Check whether or not the two given ``CTerm``s represent the same loop head."""

    @abstractmethod
    def can_make_custom_step(self, c: CTerm) -> bool: ...

    """Check whether or not the semantics can make a custom step from a given ``CTerm``."""

    @abstractmethod
    def custom_step(self, c: CTerm) -> KCFGExtendResult | None: ...

    """Implement a custom semantic step."""


class DefaultSemantics(KCFGSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        return False

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False

    def can_make_custom_step(self, c: CTerm) -> bool:
        return False

    def custom_step(self, c: CTerm) -> KCFGExtendResult | None:
        return None
