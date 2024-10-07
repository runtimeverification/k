from __future__ import annotations

from functools import reduce
from typing import TYPE_CHECKING

from pyk.cterm.cterm import cterms_anti_unify
from pyk.utils import partition, single

from .semantics import DefaultSemantics

if TYPE_CHECKING:
    from collections.abc import Callable

    from pyk.kast.outer import KDefinition

    from .kcfg import KCFG, NodeIdLike
    from .semantics import KCFGSemantics


class KCFGMinimizer:
    kcfg: KCFG
    semantics: KCFGSemantics
    kdef: KDefinition | None

    def __init__(self, kcfg: KCFG, heuristics: KCFGSemantics | None = None, kdef: KDefinition | None = None) -> None:
        if heuristics is None:
            heuristics = DefaultSemantics()
        self.kcfg = kcfg
        self.semantics = heuristics
        self.kdef = kdef

    def lift_edge(self, b_id: NodeIdLike) -> None:
        """Lift an edge up another edge directly preceding it.

        `A --M steps--> B --N steps--> C` becomes `A --(M + N) steps--> C`. Node `B` is removed.

        Args:
            b_id: the identifier of the central node `B` of a sequence of edges `A --> B --> C`.

        Raises:
            AssertionError: If the edges in question are not in place.
        """
        # Obtain edges `A -> B`, `B -> C`
        a_to_b = single(self.kcfg.edges(target_id=b_id))
        b_to_c = single(self.kcfg.edges(source_id=b_id))
        # Remove the node `B`, effectively removing the entire initial structure
        self.kcfg.remove_node(b_id)
        # Create edge `A -> C`
        self.kcfg.create_edge(
            a_to_b.source.id, b_to_c.target.id, a_to_b.depth + b_to_c.depth, a_to_b.rules + b_to_c.rules
        )

    def lift_edges(self) -> bool:
        """Perform all possible edge lifts across the KCFG.

        The KCFG is transformed to an equivalent in which no further edge lifts are possible.

        Given the KCFG design, it is not possible for one edge lift to either disallow another or
        allow another that was not previously possible. Therefore, this function is guaranteed to
        lift all possible edges without having to loop.

        Returns:
            An indicator of whether or not at least one edge lift was performed.
        """
        edges_to_lift = sorted(
            [
                node.id
                for node in self.kcfg.nodes
                if len(self.kcfg.edges(source_id=node.id)) > 0 and len(self.kcfg.edges(target_id=node.id)) > 0
            ]
        )
        for node_id in edges_to_lift:
            self.lift_edge(node_id)
        return len(edges_to_lift) > 0

    def lift_split_edge(self, b_id: NodeIdLike) -> None:
        """Lift a split up an edge directly preceding it.

        `A --M steps--> B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]` becomes
        `A --[cond_1, ..., cond_N]--> [A #And cond_1 --M steps--> C_1, ..., A #And cond_N --M steps--> C_N]`.
        Node `B` is removed.

        Args:
            b_id: The identifier of the central node `B` of the structure `A --> B --> [C_1, ..., C_N]`.

        Raises:
            AssertionError: If the structure in question is not in place.
            AssertionError: If any of the `cond_i` contain variables not present in `A`.
        """
        # Obtain edge `A -> B`, split `[cond_I, C_I | I = 1..N ]`
        a_to_b = single(self.kcfg.edges(target_id=b_id))
        a = a_to_b.source
        split_from_b = single(self.kcfg.splits(source_id=b_id))
        ci, csubsts = list(split_from_b.splits.keys()), list(split_from_b.splits.values())
        # Ensure split can be lifted soundly (i.e., that it does not introduce fresh variables)
        assert (
            len(split_from_b.source_vars.difference(a.free_vars)) == 0
            and len(split_from_b.target_vars.difference(split_from_b.source_vars)) == 0  # <-- Can we delete this check?
        )
        # Create CTerms and CSubsts corresponding to the new targets of the split
        new_cterms = [csubst(a.cterm) for csubst in csubsts]
        # Remove the node `B`, effectively removing the entire initial structure
        self.kcfg.remove_node(b_id)
        # Create the nodes `[ A #And cond_I | I = 1..N ]`.
        ai: list[NodeIdLike] = [self.kcfg.create_node(cterm).id for cterm in new_cterms]
        # Create the edges `[A #And cond_1 --M steps--> C_I | I = 1..N ]`
        for i in range(len(ai)):
            self.kcfg.create_edge(ai[i], ci[i], a_to_b.depth, a_to_b.rules)
        # Create the split `A --[cond_1, ..., cond_N]--> [A #And cond_1, ..., A #And cond_N]
        self.kcfg.create_split_by_nodes(a.id, ai)

    def lift_split_split(self, b_id: NodeIdLike) -> None:
        """Lift a split up a split directly preceding it, joining them into a single split.

        `A --[..., cond_B, ...]--> [..., B, ...]` with `B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]` becomes
        `A --[..., cond_B #And cond_1, ..., cond_B #And cond_N, ...]--> [..., C_1, ..., C_N, ...]`.
        Node `B` is removed.

        Args:
            b_id: the identifier of the node `B` of the structure
              `A --[..., cond_B, ...]--> [..., B, ...]` with `B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]`.

        Raises:
            AssertionError: If the structure in question is not in place.
        """
        # Obtain splits `A --[..., cond_B, ...]--> [..., B, ...]` and
        # `B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]-> [C_1, ..., C_N]`
        split_from_a, split_from_b = single(self.kcfg.splits(target_id=b_id)), single(self.kcfg.splits(source_id=b_id))
        splits_from_a, splits_from_b = split_from_a.splits, split_from_b.splits
        a = split_from_a.source
        list(splits_from_b.keys())
        # Ensure split can be lifted soundly (i.e., that it does not introduce fresh variables)
        assert (  # <-- Does it will be a problem when using merging nodes, because it would introduce new variables?
            len(split_from_b.source_vars.difference(a.free_vars)) == 0
            and len(split_from_b.target_vars.difference(split_from_b.source_vars)) == 0
        )
        # Remove the node `B`, thereby removing the two splits as well
        splits_from_a.pop(self.kcfg.node(b_id).id)
        self.kcfg.remove_node(b_id)
        # Create the new split `A --[..., cond_B #And cond_1, ..., cond_B #And cond_N, ...]--> [..., C_1, ..., C_N, ...]`
        self.kcfg.create_split_by_nodes(a.id, list(splits_from_a.keys()) + list(splits_from_b.keys()))

    def lift_splits(self) -> bool:
        """Perform all possible split liftings.

        The KCFG is transformed to an equivalent in which no further split lifts are possible.

        Returns:
            An indicator of whether or not at least one split lift was performed.
        """

        def _lift_split(finder: Callable, lifter: Callable) -> bool:
            result = False
            while True:
                splits_to_lift = sorted(
                    [
                        node.id
                        for node in self.kcfg.nodes
                        if (splits := self.kcfg.splits(source_id=node.id)) != []
                        and (sources := finder(target_id=node.id)) != []
                        and (source := single(sources).source)
                        and (split := single(splits))
                        and len(split.source_vars.difference(source.free_vars)) == 0
                        and len(split.target_vars.difference(split.source_vars)) == 0
                    ]
                )
                for id in splits_to_lift:
                    lifter(id)
                    result = True
                if len(splits_to_lift) == 0:
                    break
            return result

        def _fold_lift(result: bool, finder_lifter: tuple[Callable, Callable]) -> bool:
            return _lift_split(finder_lifter[0], finder_lifter[1]) or result

        return reduce(
            _fold_lift, [(self.kcfg.edges, self.lift_split_edge), (self.kcfg.splits, self.lift_split_split)], False
        )

    def merge_nodes(self) -> bool:
        """Merge targets of Split for cutting down the number of branches, using heuristics KCFGSemantics.is_mergeable.

        Side Effect: The KCFG is rewritten by the following rewrite pattern,
            - Match: A -|Split|-> A_i -|Edge|-> B_i
            - Rewrite:
                - if `B_x, B_y, ..., B_z are not mergeable` then unchanged
                - if `B_x, B_y, ..., B_z are mergeable`, then
                    - A -|Split|-> A_x or A_y or ... or A_z
                    - A_x or A_y or ... or A_z -|Edge|-> B_x or B_y or ... or B_z
                    - B_x or B_y or ... or B_z -|Split|-> B_x, B_y, ..., B_z

        Specifically, when `B_merge = B_x or B_y or ... or B_z`
        - `or`: fresh variables in places where the configurations differ
        - `Edge` in A_merged -|Edge|-> B_merge: list of merged edges is from A_i -|Edge|-> B_i
        - `Split` in B_merge -|Split|-> B_x, B_y, ..., B_z: subst for it is from A -|Split|-> A_1, A_2, ..., A_n
        :param semantics: provides the is_mergeable heuristic
        :return: whether any merge was performed
        """

        def _is_mergeable(x: KCFG.Edge | KCFG.MergedEdge, y: KCFG.Edge | KCFG.MergedEdge) -> bool:
            return self.semantics.is_mergeable(x.target.cterm, y.target.cterm)

        # ---- Match ----

        # A -|Split|> Ai -|Edge/MergedEdge|> Mergeable Bi
        sub_graphs: list[tuple[KCFG.Split, list[list[KCFG.Edge | KCFG.MergedEdge]]]] = []

        for split in self.kcfg.splits():
            _edges = [
                single(self.kcfg.general_edges(source_id=ai))
                for ai in split.target_ids
                if self.kcfg.general_edges(source_id=ai)
            ]
            _partitions = partition(_edges, _is_mergeable)
            if len(_partitions) < len(_edges):
                sub_graphs.append((split, _partitions))

        if not sub_graphs:
            return False

        # ---- Rewrite ----

        for split, edge_partitions in sub_graphs:

            # Remove the original sub-graphs
            for p in edge_partitions:
                if len(p) == 1:
                    continue
                for e in p:
                    # TODO: remove the split and edges, then safely remove the nodes.
                    self.kcfg.remove_node(e.source.id)

            # Create A -|MergedEdge|-> Merged_Bi -|Split|-> Bi, if one edge partition covers all the splits
            if len(edge_partitions) == 1:
                merged_bi_cterm, merged_bi_subst = cterms_anti_unify(
                    [edge.target.cterm for edge in edge_partitions[0]], keep_values=True, kdef=self.kdef
                )
                merged_bi = self.kcfg.create_node(merged_bi_cterm)
                self.kcfg.create_merged_edge(split.source.id, merged_bi.id, edge_partitions[0])
                self.kcfg.create_split(
                    merged_bi.id, zip([e.target.id for e in edge_partitions[0]], merged_bi_subst, strict=True)
                )
                continue

            # Create A -|Split|-> Others & Merged_Ai -|MergedEdge|-> Merged_Bi -|Split|-> Bi
            _split_nodes: list[NodeIdLike] = []
            for edge_partition in edge_partitions:
                if len(edge_partition) == 1:
                    _split_nodes.append(edge_partition[0].source.id)
                    continue
                merged_ai_cterm, _ = cterms_anti_unify(
                    [ai2bi.source.cterm for ai2bi in edge_partition], keep_values=True, kdef=self.kdef
                )
                merged_bi_cterm, merged_bi_subst = cterms_anti_unify(
                    [ai2bi.target.cterm for ai2bi in edge_partition], keep_values=True, kdef=self.kdef
                )
                merged_ai = self.kcfg.create_node(merged_ai_cterm)
                _split_nodes.append(merged_ai.id)
                merged_bi = self.kcfg.create_node(merged_bi_cterm)
                self.kcfg.create_merged_edge(merged_ai.id, merged_bi.id, edge_partition)
                self.kcfg.create_split(
                    merged_bi.id, zip([ai2bi.target.id for ai2bi in edge_partition], merged_bi_subst, strict=True)
                )
            self.kcfg.create_split_by_nodes(split.source.id, _split_nodes)

        return True

    def minimize(self, merge: bool = False) -> None:
        """Minimize KCFG by repeatedly performing the lifting transformations.

        The KCFG is transformed to an equivalent in which no further lifting transformations are possible.
        The loop is designed so that each transformation is performed once in each iteration.
        """
        repeat = True
        while repeat:
            repeat = self.lift_edges()
            repeat = self.lift_splits() or repeat

        repeat = True
        while repeat and merge:
            repeat = self.merge_nodes()
