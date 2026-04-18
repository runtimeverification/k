"""Lazy loading stubs for memory-efficient proof display.

These stubs duck-type the real KCFG classes, deferring heavy data loading
(node CTerms, cover/split CSubsts) until actually accessed for printing.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ..cterm import CSubst, CTerm
    from ..kast.inner import KInner
    from .kcfg import NodeAttr


class LazyNode:
    """Duck-types KCFG.Node. Loads CTerm from disk on first .cterm access."""

    id: int
    attrs: frozenset
    _node_path: Path
    _cterm: CTerm | None

    def __init__(self, id: int, attrs: frozenset, node_path: Path) -> None:
        self.id = id
        self.attrs = attrs
        self._node_path = node_path
        self._cterm = None

    @property
    def cterm(self) -> CTerm:
        if self._cterm is None:
            from ..cterm import CTerm

            node_dict = json.loads(self._node_path.read_text())
            self._cterm = CTerm.from_dict(node_dict['cterm'])
        return self._cterm

    def evict(self) -> None:
        """Release the loaded CTerm from memory."""
        self._cterm = None

    def __eq__(self, other: object) -> bool:
        if isinstance(other, LazyNode):
            return self.id == other.id
        # Also compare with real KCFG.Node
        return hasattr(other, 'id') and self.id == other.id

    def __hash__(self) -> int:
        return hash(self.id)

    def __lt__(self, other: object) -> bool:
        if hasattr(other, 'id'):
            return self.id < other.id
        return NotImplemented

    def __le__(self, other: object) -> bool:
        if hasattr(other, 'id'):
            return self.id <= other.id
        return NotImplemented


class APRProofStub:
    """Lightweight stub for APRProof — answers proof-level queries without loading the full proof.

    Duck-types enough of APRProof for APRProofNodePrinter.node_attrs() to work.
    Uses proof.json metadata + the KCFG for graph queries.
    """

    def __init__(self, proof_dict: dict, kcfg: object) -> None:
        self.init = int(proof_dict['init'])
        self.target = int(proof_dict['target'])
        self._terminal_ids = set(proof_dict.get('terminal') or [])
        self._bounded_ids = set(proof_dict.get('bounded') or [])
        self._refuted_ids = {int(k) for k in (proof_dict.get('node_refutations') or {}).keys()}
        self.kcfg = kcfg

    def _resolve(self, node_id: int) -> int:
        return node_id

    def is_init(self, node_id: int) -> bool:
        return node_id == self.init

    def is_target(self, node_id: int) -> bool:
        return node_id == self.target

    def is_terminal(self, node_id: int) -> bool:
        return node_id in self._terminal_ids

    def is_explorable(self, node_id: int) -> bool:
        return (
            self.kcfg.is_leaf(node_id)
            and not self.is_terminal(node_id)
            and not self.kcfg.is_stuck(node_id)
            and not self.kcfg.is_vacuous(node_id)
        )

    def is_pending(self, node_id: int) -> bool:
        return (
            self.is_explorable(node_id)
            and not self.is_target(node_id)
            and not self.is_refuted(node_id)
            and not self.is_bounded(node_id)
        )

    def is_refuted(self, node_id: int) -> bool:
        return node_id in self._refuted_ids

    def is_bounded(self, node_id: int) -> bool:
        return node_id in self._bounded_ids


class LazyCSubst:
    """Duck-types CSubst. Loads from a JSON dict on first access."""

    _raw: dict | None
    _csubst: CSubst | None

    def __init__(self, raw_dict: dict) -> None:
        self._raw = raw_dict
        self._csubst = None

    def _load(self) -> CSubst:
        if self._csubst is None:
            from ..cterm import CSubst

            self._csubst = CSubst.from_dict(self._raw)
            self._raw = None  # Release raw dict
        return self._csubst

    @property
    def constraints(self) -> tuple:
        return self._load().constraints

    @property
    def subst(self) -> object:
        return self._load().subst

    def pred(self, *args, **kwargs) -> KInner:
        return self._load().pred(*args, **kwargs)

    def to_dict(self) -> dict:
        return self._load().to_dict()

    def evict(self) -> None:
        """Release the loaded CSubst from memory, keep raw dict for reload."""
        self._csubst = None
