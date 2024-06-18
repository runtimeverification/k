from __future__ import annotations
from abc import ABC, abstractmethod

from .kcfg import KCFG, NodeIdLike
from ..cterm import CTerm, CSubst


class MatchedKCFG:
    """
    A matched KCFG subgraph.
    """

    nodes: set[int] = set()
    """The node ids in the KCFG to be rewritten."""
    edges: set[int] = set()
    """The edge ids in the KCFG to be rewritten."""
    covers: set[int] = set()
    """The cover ids in the KCFG to be rewritten."""
    splits: set[int] = set()
    """The split ids in the KCFG to be rewritten."""
    ndbranches: set[int] = set()
    """The ndbranch ids in the KCFG to be rewritten."""


class NewKCFG:
    """
    A new KCFG subgraph.

    Motivation: NewKCFG
    1. is side effect free for the original KCFG until commit rewrite.
    2. is available to describe edges without nodes.
    3. is available to describe edges combine the nodes in NewKCFG and KCFG.

    Specifically, if the nodes of the edges are in the NewKCFG, it should be in the type of NewKCFG.Node.
    Otherwise, it should be the identifier of the node in the KCFG.
    """

    class Node:
        id: int | None
        node: CTerm

    class Edge:
        source: NewKCFG.Node | int
        target: NewKCFG.Node | int
        depth: int
        rules: tuple[str, ...]

    class Cover:
        source: NewKCFG.Node | int
        target: NewKCFG.Node | int
        csubst: CSubst

    class Split:
        source: NewKCFG.Node | int
        targets: tuple[tuple[NewKCFG.Node | int, CSubst], ...]

    class NDBranch:
        source: NewKCFG.Node | int
        targets: tuple[NewKCFG.Node | int, ...]
        rules: tuple[str, ...]

    _id_count = 0
    nodes: list[Node] = []
    """The new nodes to be added to the KCFG."""
    edges: list[Edge] = []
    """The new edges to be added to the KCFG."""
    covers: list[Cover] = []
    """The new covers to be added to the KCFG."""
    splits: list[Split] = []
    """The new splits to be added to the KCFG."""
    ndbranches: list[NDBranch] = []
    """The new ndbranches to be added to the KCFG."""

    def create_node(self, node: CTerm) -> NewKCFG.Node:
        node = NewKCFG.Node()
        node.id = self._id_count
        node.node = node
        self._id_count += 1
        return node

    def push_edge(self, source: NewKCFG.Node | int, target: NewKCFG.Node | int, depth: int, rules: tuple[str, ...]):
        edge = NewKCFG.Edge()
        edge.source = source
        edge.target = target
        edge.depth = depth
        edge.rules = rules
        self.edges.append(edge)

    def push_cover(self, source: NewKCFG.Node | int, target: NewKCFG.Node | int, csubst: CSubst):
        cover = NewKCFG.Cover()
        cover.source = source
        cover.target = target
        cover.csubst = csubst
        self.covers.append(cover)

    def push_split(self, source: NewKCFG.Node | int, targets: tuple[tuple[NewKCFG.Node | int, CSubst], ...]):
        split = NewKCFG.Split()
        split.source = source
        split.targets = targets
        self.splits.append(split)

    def push_ndbranch(self, source: NewKCFG.Node | int, targets: tuple[NewKCFG.Node | int, ...], rules: tuple[str, ...]):
        ndbranch = NewKCFG.NDBranch()
        ndbranch.source = source
        ndbranch._targets = targets
        ndbranch.rules = rules
        self.ndbranches.append(ndbranch)


class KCFGRewriter:
    """
    KCFGRewriter is used to rewrite the KCFG during the optimization / minimization process.
    """

    kcfg: KCFG
    """The KCFG to be rewritten."""

    def __init__(self, kcfg: KCFG):
        self.kcfg = kcfg

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

    def replace_sub_kcfg(self, old_kcfg: MatchedKCFG, new_kcfg: NewKCFG):
        """
        Replace the old_kcfg with the new_kcfg in the KCFG.

        Input: The old_kcfg to be replaced, and the new_kcfg to replace it.
        Effect: The old_kcfg will be replaced with the new_kcfg in the KCFG.
        """
        # Delete the old_kcfg
        for edge_id in old_kcfg.edges:
            self.kcfg._edges.pop(edge_id)
        for cover_id in old_kcfg.covers:
            self.kcfg._covers.pop(cover_id)
        for split_id in old_kcfg.splits:
            self.kcfg._splits.pop(split_id)
        for ndbranch_id in old_kcfg.ndbranches:
            self.kcfg._ndbranches.pop(ndbranch_id)
        for node_id in old_kcfg.nodes:
            self.remove_node_safe(node_id)
        # Add the new_kcfg
        for idx, node in enumerate(new_kcfg.nodes):
            kcfg_node = self.kcfg.create_node(node.node)
            new_kcfg.nodes[idx].id = kcfg_node.id
        for edge in new_kcfg.edges:
            source = edge.source.id if isinstance(edge.source, NewKCFG.Node) else edge.source
            target = edge.target.id if isinstance(edge.target, NewKCFG.Node) else edge.target
            self.kcfg.create_edge(source, target, edge.depth, edge.rules)
        for cover in new_kcfg.covers:
            source = cover.source.id if isinstance(cover.source, NewKCFG.Node) else cover.source
            target = cover.target.id if isinstance(cover.target, NewKCFG.Node) else cover.target
            self.kcfg.create_cover(source, target, cover.csubst)
        for split in new_kcfg.splits:
            source = split.source.id if isinstance(split.source, NewKCFG.Node) else split.source
            targets = [(target.id if isinstance(target, NewKCFG.Node) else target, csubst) for target, csubst in split.targets]
            self.kcfg.create_split(source, targets)
        for ndbranch in new_kcfg.ndbranches:
            source = ndbranch.source.id if isinstance(ndbranch.source, NewKCFG.Node) else ndbranch.source
            targets = [target.id if isinstance(target, NewKCFG.Node) else target for target in ndbranch.targets]
            self.kcfg.create_ndbranch(source, targets, ndbranch.rules)


class KCFGRewritePattern(ABC):
    """
    A rewrite pattern matching on a KCFG.
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



