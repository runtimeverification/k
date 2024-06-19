from __future__ import annotations
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from typing import final

from .kcfg import KCFG, NodeIdLike
from ..cterm import CTerm, CSubst
from ..utils import single


@final
@dataclass(frozen=True)
class Pats:
    """
    The matching patterns for the KCFG, starting from a node N.

    Format: source`->`target(`*`)?`|`edge_type

    Examples:
        - `S->N|edge` : Match an Edge: from node S to node N.
        - `N->T|edge` : Match an Edge: from node N to node T.
        - `S->T|edge` : Match an Edge: from node S to node T.
        - `S->T*|split` : Match an Split: from node S to nodes T*.
    """

    source: tuple[str, bool]
    target: tuple[str, bool]
    edge_type: str

    def __init__(self, pattern: str) -> None:
        # todo: add validity check
        source_org, tmp = pattern.split('->')
        target_org, edge_type = tmp.split('|')
        source, source_star = source_org.split('*')[0], '*' in source_org
        target, target_star = target_org.split('*')[0], '*' in target_org
        self.__setattr__('source', (source, source_star))
        self.__setattr__('target', (target, target_star))
        self.__setattr__('edge_type', edge_type)

    def __str__(self) -> str:
        return f"{self.source[0]}{'*' if self.source[1] else ''}->" \
               f"{self.target[0]}{'*' if self.target[1] else ''}|{self.edge_type}"


class KCFGRewriter:
    """
    KCFGRewriter is used to rewrite the KCFG during the optimization / minimization process.
    """

    kcfg: KCFG
    """The KCFG to be rewritten."""
    nodes: dict[str, KCFG.Node]
    """The nodes of the matched KCFG."""
    edges: dict[str, KCFG.Successor]
    """The edges of the matched KCFG."""

    def __init__(self, kcfg: KCFG):
        self.kcfg = kcfg

    def commit(
            self,
            node: NodeIdLike,
            match_pattern: tuple[Pats | str, ...],
            rewrite_pattern: tuple[Pats | str, ...]
    ) -> bool:
        """
        Match a subgraph of KCFG, and rewrite it.

        Input:
                - The node id to start matching. ( N )
                - The patterns to match. in the form of (A->N, N->B)
                - The patterns to rewrite. in the form of (A->B)
        Effect: The KCFG will be rewritten according to the rewrite patterns.
                Match the match_pattern and rewrite it to the rewrite_pattern.
        Output: True if the KCFG was mutated.
        """
        old_kcfg = self.match(node, match_pattern)
        if not old_kcfg:
            return False
        new_kcfg = self.create(node, rewrite_pattern, match_pattern, old_kcfg)
        self.replace(old_kcfg, new_kcfg)
        return True

    def match(
            self,
            node: NodeIdLike,
            patterns: tuple[Pats | str, ...] | None = None
    ) -> KCFG | None:
        """
        Match a subgraph of KCFG.

        Input:
              - The node id to start matching.
              - The patterns to match. If None, just return the node.
        Effect: The KCFGRewriter.nodes and KCFGRewriter.edges will be populated with the matched subgraph.
        Output: The matched subgraph.
        """
        matched = KCFG()
        is_matched = False
        matched._node_id = self.kcfg._node_id
        matched.add_node(self.kcfg.get_node(node))
        if not patterns:
            return matched
        patterns = tuple(Pats(p) if isinstance(p, str) else p for p in patterns)
        for pattern in patterns:
            if pattern == Pats.S_EDGE_N:
                edge = single(self.kcfg.edges(target_id=node))
                matched._edges[edge.source.id] = edge
                matched.add_node(edge.source)
                is_matched = True
                continue
            if pattern == Pats.N_EDGE_T:
                edge = single(self.kcfg.edges(source_id=node))
                matched._edges[node] = edge
                matched.add_node(edge.target)
                is_matched = True
                continue
            if 'N' not in pattern.value:
                raise ValueError(f"Pattern {pattern} must contain 'N' to match the current Node.")
            raise NotImplementedError(f"Pattern {pattern} is not implemented.")
        if not is_matched:
            return None
        return matched

    def create(
            self,
            node: NodeIdLike,
            rewrite_patterns: tuple[Pats | str, ...],
            match_patterns: tuple[Pats | str, ...],
            old_kcfg: KCFG
    ) -> KCFG:
        """
        Create a new KCFG by rewriting the matched subgraph.

        Input:
              - The node id to start creating.
              - The patterns to rewrite / create.
              - The matched subgraph.
        Output: The new KCFG.
        """
        new_kcfg = KCFG()
        for pattern in rewrite_patterns:
            # parse / desugar the source and target of the pattern
            source, target, edge_type = pattern.edge()

            def _desugar(n: str) -> tuple[tuple(KCFG.Node, KCFG.Edge), ...]:
                for match_pattern in match_patterns:
                    if n in match_pattern.value:
                        source_m, target_m, edge_type_m = match_pattern.edge()
                        # todo: S*, T*; cannot find directly like S* | S;  T* | T
                        # todo: split ...
                        if n == source_m:
                            if edge_type_m == 'edge':
                                return tuple((node, edge) for edge in old_kcfg.edges(target_id=node))
                        if n == target_m:
                            if edge_type_m == 'edge':
                                return tuple((edge.target, edge) for edge in old_kcfg.edges(target_id=node))
                raise ValueError(f"Pattern {match_patterns} must contain '{n}' to match the current Node.")
            source = _desugar(source)
            target = _desugar(target)


        return new_kcfg

    # todo: move it to kcfg.py, maybe as a argument of remove_node
    def remove_node_safe(self, node_id: int) -> bool:
        """
        Remove the node from the KCFG safely.
        This function will do nothing if there are any EdgeLike that reference the node.

        Input: The node id to be removed.
        Effect: The node will be removed from the KCFG.
        Output: True if the node was removed.
        """
        if len(self.kcfg.predecessors(node_id)) > 0 or len(self.kcfg.successors(node_id)) > 0:
            return False
        node = self.kcfg._nodes.pop(node_id)
        self.kcfg._created_nodes.discard(node_id)
        self.kcfg._deleted_nodes.add(node.id)
        return True

    def _commit(self, old_kcfg: KCFG, new_kcfg: KCFG):
        """
        Replace the old_kcfg with the new_kcfg in the KCFG.

        Input: The old_kcfg to be replaced, and the new_kcfg to replace it.
        Effect: The old_kcfg will be replaced with the new_kcfg in the KCFG.
        """

        def update_elements(old_elements, new_elements, storage):
            for elem_id in old_elements:
                if elem_id not in new_elements:
                    storage.pop(elem_id, None)
                else:
                    new_elements.pop(elem_id, None)
            storage.update(new_elements)

        # Update edges, covers, splits, and ndbranches
        update_elements(old_kcfg._edges, new_kcfg._edges, self.kcfg._edges)
        update_elements(old_kcfg._covers, new_kcfg._covers, self.kcfg._covers)
        update_elements(old_kcfg._splits, new_kcfg._splits, self.kcfg._splits)
        update_elements(old_kcfg._ndbranches, new_kcfg._ndbranches, self.kcfg._ndbranches)

        # Update nodes
        for node_id in old_kcfg._nodes:
            if node_id not in new_kcfg._nodes:
                self.remove_node_safe(node_id)
            else:
                new_kcfg._nodes.pop(node_id)
        for node_id, node in new_kcfg._nodes.items():
            if not self.kcfg.get_node(node_id):
                self.kcfg.add_node(node)

        # Update node_id if necessary;
        # make sure the create_node will not create a node with the same id
        if new_kcfg._node_id > self.kcfg._node_id:
            self.kcfg._node_id = new_kcfg._node_id


class KCFGRewritePattern(ABC):
    """
    A side-effect free rewrite pattern matching on a KCFG.
    """

    # todo: benefit and priority

    @abstractmethod
    def match_and_rewrite(self, node: NodeIdLike, rewriter: KCFGRewriter) -> bool:
        """
        Match a subgraph of KCFG, and optionally perform a rewrite using the rewriter.
        """
        ...


class KCFGRewriteWalker:
    """
    Walks through the KCFG and rewrite the KCFG.
    The walker will visit each node in the KCFG and rewrite the node according to the rewrite patterns.
    The walker will also walk recursively on the created nodes.
    """

    patterns: list[KCFGRewritePattern]
    _work_list: list[NodeIdLike]

    def __init__(
            self,
            patterns: list[KCFGRewritePattern],
    ):
        self.patterns = patterns
        self._work_list = []

    def rewrite(self, kcfg: KCFG) -> bool:
        """
        Rewrite the KCFG recursively, until no more rewrites are possible.

        Input: The KCFG to be rewritten.
        Effect: The KCFG will be rewritten according to the rewrite patterns.
        Output: True if the KCFG was mutated.
        """

        self._populate_work_list(kcfg)
        was_modified = self._process_work_list(kcfg)

        result = was_modified

        while was_modified:
            self._populate_work_list(kcfg)
            was_modified = self._process_work_list(kcfg)
        return result

    def _populate_work_list(self, kcfg: KCFG) -> None:
        """
        Populate the work list with the nodes that need to be rewritten.

        Effect: The _work_list will be populated with all the node ids in the KCFG.
        """
        self._work_list = list(node.id for node in kcfg.nodes)

    def _process_work_list(self, kcfg: KCFG) -> bool:
        """
        Process the _work_list until it is empty.

        Input: The KCFG to be processed.
        Effect: The KCFG will be rewritten according to the rewrite patterns. (Just Once)
        Output: True if any modification was done.
        """
        was_modified = False
        rewriter = KCFGRewriter(kcfg)
        while self._work_list:
            node = self._work_list.pop()
            for pattern in self.patterns:
                if rewriter.kcfg.get_node(node):
                    was_modified |= pattern.match_and_rewrite(node, rewriter)
        return was_modified
