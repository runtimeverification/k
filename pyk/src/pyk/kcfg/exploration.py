from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kcfg.kcfg import KCFG, NodeAttr
from pyk.kcfg.minimize import KCFGMinimizer

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from typing import Any

    from pyk.kcfg.kcfg import NodeIdLike


class KCFGExplorationNodeAttr(NodeAttr):
    TERMINAL = NodeAttr('terminal')


class KCFGExploration:
    kcfg: KCFG

    def __init__(self, kcfg: KCFG, terminal: Iterable[NodeIdLike] | None = None) -> None:
        self.kcfg = kcfg
        if terminal:
            for node_id in terminal:
                self.add_terminal(node_id)

    @property
    def terminal_ids(self) -> set[int]:
        return {node.id for node in self.kcfg.nodes if KCFGExplorationNodeAttr.TERMINAL in node.attrs}

    #
    # Recognisers
    #

    # Terminal node recogniser
    def is_terminal(self, node_id: NodeIdLike) -> bool:
        return KCFGExplorationNodeAttr.TERMINAL in self.kcfg.node(node_id).attrs

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
        self.kcfg.add_attr(node_id, KCFGExplorationNodeAttr.TERMINAL)

    # Unmarking a given node as terminal
    def remove_terminal(self, node_id: int) -> None:
        self.kcfg.remove_attr(node_id, KCFGExplorationNodeAttr.TERMINAL)

    #
    # Lifted KCFG functions that may affect terminal nodes
    #

    # Removing a given node
    def remove_node(self, node_id: NodeIdLike) -> None:
        node_id = self.kcfg._resolve(node_id)
        self.kcfg.remove_node(node_id)

    # Pruning a KCFG subtree starting from a given node
    def prune(self, node_id: NodeIdLike, keep_nodes: Iterable[NodeIdLike] = ()) -> list[int]:
        return self.kcfg.prune(node_id, keep_nodes=keep_nodes)

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
        dct['terminal'] = sorted(node.id for node in self.kcfg.nodes if self.is_terminal(node.id))
        return dct

    #
    # Minimization
    #

    # Minimizing the KCFG
    def minimize_kcfg(self) -> None:
        KCFGMinimizer(self.kcfg).minimize()
