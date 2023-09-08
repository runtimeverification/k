from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kcfg.kcfg import KCFG

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from typing import Any

    from pyk.kcfg.kcfg import NodeIdLike


class KCFGExploration:
    kcfg: KCFG
    _terminal: set[int]

    def __init__(self, kcfg: KCFG, terminal: Iterable[NodeIdLike] | None = None) -> None:
        self.kcfg = kcfg
        self._terminal = {kcfg._resolve(node_id) for node_id in terminal} if terminal is not None else set()

    #
    # Recognisers
    #

    # Terminal node recogniser
    def is_terminal(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) in self._terminal

    # Explorable node recogniser
    def is_explorable(self, node_id: NodeIdLike) -> bool:
        return (
            self.kcfg.is_leaf(node_id)
            and not self.is_terminal(node_id)
            and not self.kcfg.is_stuck(node_id)
            and not self.kcfg.is_vacuous(node_id)
        )

    #
    # Collectors
    #

    # Terminal node collector
    @property
    def terminal(self) -> list[KCFG.Node]:
        return [node for node in self.kcfg.nodes if self.is_terminal(node.id)]

    # Explorable node collector
    @property
    def explorable(self) -> list[KCFG.Node]:
        return [node for node in self.kcfg.leaves if self.is_explorable(node.id)]

    #
    # Terminal node manipulation
    #

    # Marking a given node as terminal
    def add_terminal(self, node_id: NodeIdLike) -> None:
        self._terminal.add(self.kcfg._resolve(node_id))

    # Unmarking a given node as terminal
    def remove_terminal(self, node_id: int) -> None:
        self._terminal.discard(node_id)

    #
    # Lifted KCFG functions that may affect terminal nodes
    #

    # Removing a given node
    def remove_node(self, node_id: NodeIdLike) -> None:
        node_id = self.kcfg._resolve(node_id)
        self.kcfg.remove_node(node_id)
        self.remove_terminal(node_id)

    # Pruning a KCFG subtree starting from a given node
    def prune(self, node_id: NodeIdLike, keep_nodes: Iterable[NodeIdLike] = ()) -> list[int]:
        pruned_nodes = self.kcfg.prune(node_id, keep_nodes=keep_nodes)
        for node_id in pruned_nodes:
            self.remove_terminal(node_id)
        return pruned_nodes

    #
    # Dictionarisation
    #

    # Conversion from dictionary
    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> KCFGExploration:
        kcfg = KCFG.from_dict(dct['kcfg'])
        terminal = dct['terminal']

        return KCFGExploration(kcfg, terminal)

    # Conversion to dictionary
    def to_dict(self) -> dict[str, Any]:
        dct: dict[str, Any] = {}
        dct['kcfg'] = self.kcfg.to_dict()
        dct['terminal'] = sorted(self._terminal)
        return dct
