from .rewriter import KCFGRewriter, KCFGRewritePattern, NodeIdLike, KCFGRewriteWalker
from .kcfg import KCFG


def minimize_kcfg(kcfg: KCFG) -> None:
    """
    Minimize KCFG by repeatedly performing the transformations.

    Input: KCFG to be minimized.

    Effect: The KCFG is transformed to an equivalent in which no further patterns are matched.
            - LiftEdgeEdge
            - LiftSplitSplit
            - LiftEdgeSplit
            - MergeSplitNodes

    Output: None
    """
    walker = KCFGRewriteWalker([
        LiftEdgeEdge(),
        # LiftSplitSplit(),
        # LiftEdgeSplit(),
        # MergeSplitNodes(),
    ])
    walker.rewrite(kcfg)


# todo: the best way to describe and perform
#  this kind of reasoning and transformation
#  should be something like a Knowledge Graph.
#  And I think it's not hard to implement it for KCFG.
class LiftEdgeEdge(KCFGRewritePattern):
    def match_and_rewrite(self, node: NodeIdLike, rewriter: KCFGRewriter) -> bool:
        match_pattern = ('S->N|edge', 'N->T|edge',)
        rewrite_pattern = ('S->T|edge',)
        return rewriter.commit(node, match_pattern, rewrite_pattern)


class LiftSplitSplit(KCFGRewritePattern):
    def match_and_rewrite(self, node: NodeIdLike, rewriter: KCFGRewriter) -> bool:
        match_pattern = ('S->N|split', 'N->T*|split',)
        rewrite_pattern = ('S->S*|split', 'S*->T*|edge',)
        return rewriter.commit(node, match_pattern, rewrite_pattern)


class LiftEdgeSplit(KCFGRewritePattern):
    def match_and_rewrite(self, node: NodeIdLike, rewriter: KCFGRewriter) -> bool:
        match_pattern = ('S->N|edge', 'N->T*|split',)
        rewrite_pattern = ('S->S*|split', 'S*->T*|edge',)
        return rewriter.commit(node, match_pattern, rewrite_pattern)


class MergeSplitNodes(KCFGRewritePattern):
    def match_and_rewrite(self, node: NodeIdLike, rewriter: KCFGRewriter) -> bool:
        match_pattern = ('N->S*|split', 'S*->T*|edge',)
        rewrite_pattern = ('N->T|edge', 'T->T*|split',)
        return rewriter.commit(node, match_pattern, rewrite_pattern)