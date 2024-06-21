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

    Format: source`->`target(`*`)?`|`edge_type. Note that
    1. `N` is preserved for representing the current node.
    2. `N` must exist in the match pattern.
    3. ` ` is not allowed in the pattern.

    Examples:
        - `S->N|edge` : Match an Edge: from node S to node N.
        - `N->T|edge` : Match an Edge: from node N to node T.
        - `S->T|edge` : Match an Edge: from node S to node T.
        - `S->T*|split` : Match an Split: from node S to nodes T*.
    """
    # todo: we should allow the pattern similar to the KG search statements.
    # todo: we should release the constraints on the pattern. For example, `N` can be missed.

    source: str
    is_multi_source: bool
    target: str
    is_multi_target: bool
    edge_type: str

    def __init__(self, pattern: str) -> None:
        # todo: add validity check
        source, tmp = pattern.split('->')
        target, edge_type = tmp.split('|')
        source_star = source.endswith('*')
        target_star = target.endswith('*')
        self.__setattr__('source', source)
        self.__setattr__('is_multi_source', source_star)
        self.__setattr__('target', target)
        self.__setattr__('is_multi_target', target_star)
        self.__setattr__('edge_type', edge_type)

    def __str__(self) -> str:
        return f"{self.source}->{self.target}|{self.edge_type}"


class KCFGRewriter:
    """
    KCFGRewriter is used to rewrite the KCFG during the optimization / minimization process.
    """

    kcfg: KCFG
    """The KCFG to be rewritten."""
    _nodes: dict[str, tuple[KCFG.Node, ...]]
    """The nodes of the matched KCFG."""
    _edges: dict[str, tuple[KCFG.Successor, ...]]
    """The edges of the matched KCFG."""

    def __init__(self, kcfg: KCFG):
        self.kcfg = kcfg

    def commit(
            self,
            node: NodeIdLike,
            match_pattern: tuple[str, ...],
            rewrite_pattern: tuple[str, ...]
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
        new_kcfg = self.create(rewrite_pattern)
        self.replace(old_kcfg, new_kcfg)  # todo: not implemented yet
        return True

    def match(
            self,
            node_id: NodeIdLike,
            patterns: tuple[str, ...] | None = None
    ) -> KCFG | None:
        """
        Match a subgraph of KCFG.

        Input:
              - The node id to start matching.
              - The patterns to match. If None, just return the node.
        Effect: The KCFGRewriter.nodes and KCFGRewriter.edges will be populated with the matched subgraph.
        Output: The matched subgraph.
        """
        # the patterns are effective when constructed like this: N->A, A->B, B->C
        # the patterns are not effective when constructed like this: B->C, A->B, N->A

        # initialization
        self._nodes.clear()
        self._edges.clear()
        # add current node to the matched KCFG
        node = self.kcfg.get_node(node_id)
        # add the current node to the nodes
        self._nodes['N'] = (node,)
        # if no patterns, just return the node
        if not patterns:
            return self._get_matched()
        # parse the patterns
        patterns = [Pats(p) for p in patterns]
        # match the patterns
        loop_count = -1
        # the worst case is that only one pattern is matched in each loop
        # n + (n-1) + ... + 1 = n(n+1)/2
        max_loop = (len(patterns) * (len(patterns) + 1)) / 2
        while len(patterns) > 0:
            loop_count += 1
            pattern = patterns.pop(0)
            source = self._nodes.get(pattern.source)
            target = self._nodes.get(pattern.target)
            if not source or not target:
                # if greater than the max loop, raise an error.
                if loop_count > max_loop:
                    raise ValueError(f"Patterns {patterns} cannot be matched started from current Node `N`.")
                patterns.append(pattern)
                continue
            # match the pattern
            source_edge = set()
            target_edge = set()
            for src in source:
                tmp = getattr(self.kcfg, f"{pattern.edge_type}s")(source_id=src.id)
                if len(tmp) > 0:
                    source_edge.update(tmp)
            for tgt in target:
                tmp = getattr(self.kcfg, f"{pattern.edge_type}s")(target_id=tgt.id)
                if len(tmp) > 0:
                    target_edge.update(tmp)
            # check the match
            if len(source_edge) > 0 and len(target_edge) > 0:
                if source_edge == target_edge:
                    self._edges[str(pattern)] = tuple(source_edge)
                else:
                    return None
            if len(source_edge) == 0 and len(target_edge) == 0:
                return None
            if len(source_edge) > 0:
                node_tmp = []
                for edge in source_edge:
                    if isinstance(edge, KCFG.MultiEdge):
                        for target in edge.targets:
                            node_tmp.append(self.kcfg.get_node(target))
                    else:
                        node_tmp.append(self.kcfg.get_node(edge.target))
                self._nodes[pattern.target] = tuple(node_tmp)
                self._edges[str(pattern)] = tuple(source_edge)
            if len(target_edge) > 0:
                node_tmp = []
                for edge in target_edge:
                    node_tmp.append(self.kcfg.get_node(edge.source))
                self._nodes[pattern.source] = tuple(node_tmp)
                self._edges[str(pattern)] = tuple(target_edge)
        return self._get_matched()

    def _get_matched(
            self,
            nodes: dict[str, tuple[KCFG.Node, ...]] = None,
            edges: dict[str, tuple[KCFG.Successor, ...]] = None
    ) -> KCFG:
        matched = KCFG()
        nodes_tmp = nodes if nodes else self._nodes
        edges_tmp = edges if edges else self._edges
        matched._node_id = self.kcfg._node_id
        for ns in nodes_tmp.values():
            for node in ns:
                matched.add_node(node)
                matched._node_id = max(matched._node_id, node.id)
        for es in edges_tmp.values():
            for edge in es:
                matched.add_successor(edge)
        return matched

    def create(
            self,
            rewrite_patterns: tuple[str, ...],
    ) -> KCFG:
        """
        Create a new KCFG by rewriting the matched subgraph.

        Input: The patterns to rewrite / create.
        Output: The new KCFG.
        """
        # initialization
        nodes: dict[str, tuple[KCFG.Node, ...]] = {}
        edges: dict[str, tuple[KCFG.Successor, ...]] = {}
        patterns = [Pats(p) for p in rewrite_patterns]
        for pattern in patterns:
            # todo: we just support patterns that we need for minimization. We should support more patterns if needed.
            source = self._nodes.get(pattern.source)
            target = self._nodes.get(pattern.target)
            if not source or not target:
                raise NotImplementedError(f"Pattern {pattern} is not supported.")
            match pattern.edge_type:
                case 'edge':
                    if pattern.is_multi_source and pattern.is_multi_target:
                        raise NotImplementedError(f"Pattern {pattern} is not supported.")
                    elif not pattern.is_multi_source and not pattern.is_multi_target:
                        assert len(source) == 1 and len(target) == 1, \
                            (f"source and target should be single node for {pattern}, "
                             f"but found {len(source)} and {len(target)}")
                        source_node = source[0]
                        target_node = target[0]
                        depth, rules = self.merge_paths(source_node.id, target_node.id)
                        edges[str(pattern)] = (KCFG.Edge(
                            source_node,
                            target_node,
                            depth,
                            tuple(rules)
                        ),)
                    else:
                        raise ValueError(f"Pattern {pattern} is illegal for Edge.")
                case _:
                    # todo: not implemented yet
                    raise NotImplementedError(f"Pattern {pattern} is not supported.")
        return self._get_matched(nodes, edges)

    def merge_paths(self, source: int, target: int) -> tuple[int, tuple[str, ...]]:
        """
        Merge the paths from source to target.

        Input: The identifiers of source and target nodes.
        Output: The depth and the rules of the merged paths.
        """
        successors = self.kcfg.shortest_path_between(source, target)
        depth = 0
        rules = []
        for succ in successors:
            match succ:
                case KCFG.Edge(_, _, d, r):
                    depth += d
                    rules.extend(r)
                case KCFG.NDBranch(_, t, r):
                    # 匹配到target在t中的位置，然后取r的相同位置
                    target_node = self.kcfg.get_node(target)
                    idx = t.index(target_node)
                    depth += 1
                    rules.append(r[idx])
                case _:
                    continue
        return depth, tuple(rules)

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
