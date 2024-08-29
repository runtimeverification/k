from __future__ import annotations

from functools import reduce
from typing import TYPE_CHECKING

from ..cterm import CTerm
from ..utils import not_none, single

if TYPE_CHECKING:
    from collections.abc import Callable

    from .kcfg import KCFG, NodeIdLike


class KCFGMinimizer:
    kcfg: KCFG

    def __init__(self, kcfg: KCFG) -> None:
        self.kcfg = kcfg

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
            and len(split_from_b.target_vars.difference(split_from_b.source_vars)) == 0
        )
        # Create CTerms and CSubsts corresponding to the new targets of the split
        new_cterms_with_constraints = [
            (CTerm(a.cterm.config, a.cterm.constraints + csubst.constraints), csubst.constraint) for csubst in csubsts
        ]
        # Generate substitutions for new targets, which all exist by construction
        new_csubsts = [
            not_none(a.cterm.match_with_constraint(cterm)).add_constraint(constraint)
            for (cterm, constraint) in new_cterms_with_constraints
        ]
        # Remove the node `B`, effectively removing the entire initial structure
        self.kcfg.remove_node(b_id)
        # Create the nodes `[ A #And cond_I | I = 1..N ]`.
        ai: list[NodeIdLike] = [self.kcfg.create_node(cterm).id for (cterm, _) in new_cterms_with_constraints]
        # Create the edges `[A #And cond_1 --M steps--> C_I | I = 1..N ]`
        for i in range(len(ai)):
            self.kcfg.create_edge(ai[i], ci[i], a_to_b.depth, a_to_b.rules)
        # Create the split `A --[cond_1, ..., cond_N]--> [A #And cond_1, ..., A #And cond_N]
        self.kcfg.create_split(a.id, zip(ai, new_csubsts, strict=True))

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
        ci = list(splits_from_b.keys())
        # Ensure split can be lifted soundly (i.e., that it does not introduce fresh variables)
        assert (
            len(split_from_b.source_vars.difference(a.free_vars)) == 0
            and len(split_from_b.target_vars.difference(split_from_b.source_vars)) == 0
        )
        # Get the substitution for `B`, at the same time removing 'B' from the targets of `A`.
        csubst_b = splits_from_a.pop(self.kcfg.node(b_id).id)
        # Generate substitutions for additional targets `C_I`, which all exist by construction;
        # the constraints are cumulative, resulting in `cond_B #And cond_I`
        additional_csubsts = [
            not_none(a.cterm.match_with_constraint(self.kcfg.node(ci).cterm))
            .add_constraint(csubst_b.constraint)
            .add_constraint(csubst.constraint)
            for ci, csubst in splits_from_b.items()
        ]
        # Create the targets of the new split
        ci = list(splits_from_b.keys())
        new_splits = zip(
            list(splits_from_a.keys()) + ci, list(splits_from_a.values()) + additional_csubsts, strict=True
        )
        # Remove the node `B`, thereby removing the two splits as well
        self.kcfg.remove_node(b_id)
        # Create the new split `A --[..., cond_B #And cond_1, ..., cond_B #And cond_N, ...]--> [..., C_1, ..., C_N, ...]`
        self.kcfg.create_split(a.id, new_splits)

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

    def minimize(self) -> None:
        """Minimize KCFG by repeatedly performing the lifting transformations.

        The KCFG is transformed to an equivalent in which no further lifting transformations are possible.
        The loop is designed so that each transformation is performed once in each iteration.
        """
        repeat = True
        while repeat:
            repeat = self.lift_edges()
            repeat = self.lift_splits() or repeat
