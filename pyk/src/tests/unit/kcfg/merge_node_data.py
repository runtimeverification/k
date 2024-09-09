from __future__ import annotations

from pyk.kast.inner import KVariable
from pyk.prelude.kint import intToken

from ..kcfg.prelude import ge_ml, lt_ml

from pyk.cterm import CTerm
from pyk.kcfg import KCFG
from pyk.kcfg.semantics import DefaultSemantics
from ..utils import k


def merge_node_test_kcfg() -> KCFG:
    """Define a KCFG with all possible scenarios for merging nodes.

    Here are some specifications for the KCFG:
    1. Unable to continue other pattern-rewriting, e.g., lift_edge_edge, lift_split_split, lift_edge_split, ...
    2. Able to test the merged CTerms and the merged CSubsts.
    3. Able to propagate all possible result structures through different heuristics, including
       merged-into-one, merged-into-two, partially-merged-into-one, partially-merged-into-two, and not-merged.
    4. Contains Split, Edge, and MergedEdge, because the merging process is targeted at these types of edges.

    The KCFG is as follows:
    1 --> 2: Split, X <Int 0
    1 --> 3: Split, X >=Int 0 & X <Int 2
    1 --> 4: Split, X >=Int 2 & X <Int 6
    1 --> 5: Split, Y >=Int 6 & Y <Int 10
    1 --> 6: Split, 11
    1 --> 7: Split, 12
    1 --> 8: Split, Y >=Int 13
    2 --> 9: Edge, 5, (r1)
    3 --> 10: Edge, 10, (r2, r3)
    4 --> 11: MergedEdge, 15, (r4, r5) | 20, (r6)
    5 --> 12: MergedEdge, 25, (r7) | 30, (r8)
    6 --> 13: Edge, 35, (r9)
    7 --> 14: Edge, 40, (r10)
    8 --> 15: Edge, 45, (r11)

    The KCFG is visualized as follows:
    1 -> 2 -> 9
    | -> 3 -> 10
    | -> 4 -> 11
    | -> 5 -> 12
    | -> 6 -> 13
    | -> 7 -> 14
    | -> 8 -> 15
    """
    cfg = KCFG()
    # 1 <X> -10 <= X < 100
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', -10), lt_ml('X', 100)]), )
    # 2 <X> -10 <= X < 0
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', -10), lt_ml('X', 0)]))
    # 3 <X> 0 <= X < 2
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 0), lt_ml('X', 2)]))
    # 4 <X> 2 <= X < 4
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 2), lt_ml('X', 4)]))
    # 5 <Y> 4 <= Y < 6
    cfg.create_node(CTerm(k(KVariable('Y')), [ge_ml('Y', 4), lt_ml('Y', 6)]))
    # 6 <X> 6 <= X < 8
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 6), lt_ml('X', 8)]))
    # 7 <X> 8 <= Y < 10
    cfg.create_node(CTerm(k(KVariable('Y')), [ge_ml('Y', 8), lt_ml('Y', 10)]))
    # 8 <10>
    cfg.create_node(CTerm(k(intToken(10))))
    # 9 <11>
    cfg.create_node(CTerm(k(intToken(11))))
    # 10 <Z> 12 <= Z < 100
    cfg.create_node(CTerm(k(KVariable('Z')), [ge_ml('Z', 12), lt_ml('Z', 100)]))

    # 11 <X> 2 <= X < 6
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 2), lt_ml('X', 6)]))
    # 12 <Y> 6 <= Y < 10
    cfg.create_node(CTerm(k(KVariable('Y')), [ge_ml('Y', 6), lt_ml('Y', 10)]))

    # Because edge denotes multiple rewriting steps, it can end up with any node.
    # 13 <N> 12 <= N
    cfg.create_node(CTerm(k(KVariable('N')), [ge_ml('N', 12)]))
    # 14 <11>
    cfg.create_node(CTerm(k(intToken(11))))
    # 15 <10>
    cfg.create_node(CTerm(k(intToken(10))))
    # 16 <N> 8 <= N < 10
    cfg.create_node(CTerm(k(KVariable('N')), [ge_ml('N', 8), lt_ml('N', 10)]))
    # 17 <N> 6 <= N < 8
    cfg.create_node(CTerm(k(KVariable('N')), [ge_ml('N', 6), lt_ml('N', 8)]))
    # 18 <N> 4 <= N < 6
    cfg.create_node(CTerm(k(KVariable('N')), [ge_ml('N', 4), lt_ml('N', 6)]))
    # 19 <N> 2 <= N < 4
    cfg.create_node(CTerm(k(KVariable('N')), [ge_ml('N', 2), lt_ml('N', 4)]))
    # 20 <N> 0 <= N < 2
    cfg.create_node(CTerm(k(KVariable('N')), [ge_ml('N', 0), lt_ml('N', 2)]))
    # 21 <N> N < 0
    cfg.create_node(CTerm(k(KVariable('N')), [lt_ml('N', 0)]))

    return cfg


class AlwaysTrue(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        return True
