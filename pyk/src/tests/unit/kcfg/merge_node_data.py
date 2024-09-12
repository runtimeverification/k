from __future__ import annotations

from typing import TYPE_CHECKING, Final

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KLabel, KSort, KToken, KVariable
from pyk.kast.manip import ml_pred_to_bool
from pyk.kcfg import KCFG
from pyk.kcfg.semantics import DefaultSemantics
from pyk.prelude.kbool import andBool
from pyk.prelude.kint import intToken
from pyk.utils import single

from ..utils import ge_ml, k, lt_ml

if TYPE_CHECKING:
    from typing import Iterable

    from pyk.kast.inner import KInner
    from pyk.kcfg.minimize import KCFGMinimizer


def merge_node_test_kcfg() -> KCFG:
    """Define a KCFG with all possible scenarios for merging nodes.

    Here are some specifications for the KCFG:
    1. Unable to continue other pattern-rewriting, e.g., lift_edge_edge, lift_split_split, lift_edge_split, ...
    2. Able to test the merged CTerms and the merged CSubsts.
    3. Able to propagate all possible result structures through different heuristics, including
       merged-into-one, merged-into-two, partially-merged-into-one, partially-merged-into-two, and not-merged.
    4. Contains Split, Edge, and MergedEdge, because the merging process is targeted at these types of edges.
    """
    cfg = KCFG()
    # Split Source: A
    # 1 <X> -10 <= X < 100
    cfg.create_node(
        CTerm(k(KVariable('X')), [ge_ml('X', -10), lt_ml('X', 100)]),
    )

    # Split Targets & Edge Sources: Ai
    # 2 <X> -10 <= X < 0
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', -10), lt_ml('X', 0)]))
    # 3 <X> 0 <= X < 2
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 0), lt_ml('X', 2)]))
    # 4 <X> 2 <= A < 6
    cfg.create_node(CTerm(k(KVariable('A')), [ge_ml('A', 2), lt_ml('A', 6)]))
    # 5 <Y> 6 <= B < 10
    cfg.create_node(CTerm(k(KVariable('B')), [ge_ml('B', 6), lt_ml('B', 10)]))
    # 6 <10>
    cfg.create_node(CTerm(k(intToken(10))))
    # 7 <11>
    cfg.create_node(CTerm(k(intToken(11))))
    # 8 <Z> 12 <= Z < 100
    cfg.create_node(CTerm(k(KVariable('Z')), [ge_ml('Z', 12), lt_ml('Z', 100)]))

    # Edge Targets: Bi
    # 9 <1>
    cfg.create_node(CTerm(k(intToken(1))))
    # 10 <2>
    cfg.create_node(CTerm(k(intToken(2))))
    # 11 <3>
    cfg.create_node(CTerm(k(intToken(3))))
    # 12 <4>
    cfg.create_node(CTerm(k(intToken(4))))
    # 13 <5>
    cfg.create_node(CTerm(k(intToken(5))))
    # 14 <6>
    cfg.create_node(CTerm(k(intToken(6))))
    # 15 <7>
    cfg.create_node(CTerm(k(intToken(7))))

    # MergedEdge Sources
    # 16 <X> 2 <= X < 4
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 2), lt_ml('X', 4)]))
    # 17 <Y> 4 <= Y < 6
    cfg.create_node(CTerm(k(KVariable('Y')), [ge_ml('Y', 4), lt_ml('Y', 6)]))
    # 18 <X> 6 <= X < 8
    cfg.create_node(CTerm(k(KVariable('X')), [ge_ml('X', 6), lt_ml('X', 8)]))
    # 19 <X> 8 <= Y < 10
    cfg.create_node(CTerm(k(KVariable('Y')), [ge_ml('Y', 8), lt_ml('Y', 10)]))

    # MergedEdge Targets
    # 20 <8>
    cfg.create_node(CTerm(k(intToken(8))))
    # 21 <9>
    cfg.create_node(CTerm(k(intToken(9))))
    # 22 <10>
    cfg.create_node(CTerm(k(intToken(10))))
    # 23 <11>
    cfg.create_node(CTerm(k(intToken(11))))

    # MergedEdge
    e1 = cfg.create_edge(16, 20, 5, ['r1'])
    e2 = cfg.create_edge(17, 21, 6, ['r2', 'r3'])
    e3 = cfg.create_edge(18, 22, 7, ['r4', 'r5'])
    e4 = cfg.create_edge(19, 23, 8, ['r6', 'r7', 'r8'])
    cfg.remove_node(16)
    cfg.remove_node(17)
    cfg.remove_node(18)
    cfg.remove_node(19)
    cfg.remove_node(20)
    cfg.remove_node(21)
    cfg.remove_node(22)
    cfg.remove_node(23)

    # Split
    cfg.create_split_by_nodes(1, [2, 3, 4, 5, 6, 7, 8])

    # Edge
    cfg.create_edge(2, 9, 10, ['r9'])
    cfg.create_edge(3, 10, 11, ['r10', 'r11'])
    cfg.create_merged_edge(4, 11, [e1, e2])
    cfg.create_merged_edge(5, 12, [e3, e4])
    cfg.create_edge(6, 13, 14, ['r12', 'r13', 'r14'])
    cfg.create_edge(7, 14, 15, ['r15'])
    cfg.create_edge(8, 15, 16, ['r16'])

    return cfg


class MergedNo(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        return False


class MergedOne(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        return True


def util_get_token(c: CTerm) -> int:
    assert isinstance(c.config, KApply)
    x = c.config.args[0]
    assert isinstance(x, KToken)
    return int(x.token)


class MergedPartialOne0(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 3 and y < 3:
            return True
        return False


class MergedPartialOne1(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 4 and y < 4:
            return True
        return False


class MergedPartialOne2(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 5 and y < 5:
            return True
        return False


class MergedTwo0(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 3 and y < 3:
            return True
        if x >= 3 and y >= 3:
            return True
        return False


class MergedTwo1(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 4 and y < 4:
            return True
        if x >= 4 and y >= 4:
            return True
        return False


class MergedPartialTwo(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 4 and y < 4:
            return True
        if 4 <= x < 6 and 4 <= y < 6:
            return True
        return False


class MergedFail(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        x = util_get_token(c1)
        y = util_get_token(c2)
        if x < 5 and y < 5:
            return True
        if x >= 4 and y >= 4:
            return True
        return False


def util_check_constraint_element(constraint: KInner, merged_var: KInner, under_check: Iterable[int]) -> None:
    # orBool
    assert isinstance(constraint, KApply) and constraint.label == KLabel('_orBool_')
    assert isinstance(merged_var, KVariable)
    idx = 0
    count = 0
    eq_idx = 0
    for arg in constraint.args:
        # _==K_
        if isinstance(arg, KApply) and arg.label == KLabel('_==K_'):
            var = arg.args[0]
            token = arg.args[1]
            assert isinstance(var, KVariable) and isinstance(token, KToken)
            assert var == merged_var
            assert int(token.token) in under_check
            under_check = [x for x in under_check if x != int(token.token)]
            count += 1
            eq_idx = idx
        idx += 1
    if count == 2:
        assert not under_check
        return

    idx = 0 if eq_idx == 1 else 0
    # andBool
    ab = constraint.args[idx]
    assert isinstance(ab, KApply) and ab.label == KLabel('_andBool_')
    idx = 0
    for arg in ab.args:
        # x ==K y
        if isinstance(arg, KApply) and arg.label == KLabel('_==K_'):
            assert isinstance(arg.args[0], KVariable) and isinstance(arg.args[1], KVariable)
            m_idx = arg.args.index(merged_var)
            other_idx = 0 if m_idx == 1 else 1
            left_idx = 0 if idx == 1 else 1
            util_check_constraint_element(ab.args[left_idx], arg.args[other_idx], under_check)
        idx += 1


def util_check_constraint(constraint: KInner, merged_var: KVariable, under_check: Iterable[int]) -> None:
    # mlEqualsTrue
    assert isinstance(constraint, KApply) and constraint.label == KLabel(
        '#Equals', [KSort('Bool'), KSort('GeneratedTopCell')]
    )
    assert constraint.args[0] == KToken('true', KSort('Bool'))
    util_check_constraint_element(constraint.args[1], merged_var, under_check)


def check_merge_no(minimizer: KCFGMinimizer) -> None:
    minimizer.minimize()
    assert minimizer.kcfg.to_dict() == merge_node_test_kcfg().to_dict()


def check_merged_one(minimizer: KCFGMinimizer) -> None:
    minimizer.minimize()
    # 1 --> merged bi: Merged Edge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=1))
    edges = {2: 9, 3: 10, 16: 20, 17: 21, 18: 22, 19: 23, 6: 13, 7: 14, 8: 15}
    for edge in merged_edge.edges:
        assert edge.source.id in edges
        assert edge.target.id == edges[edge.source.id]
    merged_bi = merged_edge.target
    assert isinstance(merged_bi.cterm.config, KApply)
    merged_var = merged_bi.cterm.config.args[0]
    assert isinstance(merged_var, KVariable)
    merged_constraint = single(merged_bi.cterm.constraints)
    util_check_constraint(merged_constraint, merged_var, [1, 2, 3, 4, 5, 6, 7])
    # merged bi --> 9 - 15: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = {9: 1, 10: 2, 11: 3, 12: 4, 13: 5, 14: 6, 15: 7}
    for s in expected_splits:
        assert s in splits
        x = list(splits[s].subst.values())[0]
        assert isinstance(x, KToken) and int(x.token) == expected_splits[s]


def check_merged_partial_one0(minimizer: KCFGMinimizer) -> None:
    minimizer.merge_nodes()
    # merged 9 - 10, else unchanged
    # 1 --> merged ai (2,3) & 4 - 8: Split
    split = single(minimizer.kcfg.splits(source_id=1))
    splits = split.splits
    expected_splits = [4, 5, 6, 7, 8, 24]
    assert all(s in splits for s in expected_splits)
    merged_ai = minimizer.kcfg.node(24)
    merged_ai_c = single(merged_ai.cterm.constraints)
    expected_ai_c = KLabel('#Equals', [KSort('Bool'), KSort('GeneratedTopCell')])(
        KToken('true', KSort('Bool')),
        KLabel('_orBool_')(
            andBool([ml_pred_to_bool(c) for c in merge_node_test_kcfg().node(3).cterm.constraints]),
            andBool([ml_pred_to_bool(c) for c in merge_node_test_kcfg().node(2).cterm.constraints]),
        ),
    )
    assert merged_ai_c == expected_ai_c
    # merged ai (2,3) --> merged bi (9,10): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=24))
    edges = {2: 9, 3: 10}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (9,10) --> 9 - 10: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [9, 10]
    assert all(s in splits for s in expected_splits)
    # 4 - 8 --> 11 - 15: Edge (unchanged)
    for i in range(4, 6):
        medge = single(minimizer.kcfg.merged_edges(source_id=i))
        assert medge.target.id == i + 7
    for i in range(6, 9):
        edge = single(minimizer.kcfg.edges(source_id=i))
        assert edge.target.id == i + 7


def check_merged_partial_one1(minimizer: KCFGMinimizer) -> None:
    minimizer.merge_nodes()
    # merged 9 - 11, else unchanged
    # 1 --> merged ai (2,3,4) & 5 - 8: Split
    split = single(minimizer.kcfg.splits(source_id=1))
    splits = split.splits
    expected_splits = [5, 6, 7, 8, 24]
    assert all(s in splits for s in expected_splits)
    # merged ai (2,3,4) --> merged bi (9,10,11): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=24))
    # edges = {2: 9, 3: 10, 4: 11}
    edges = {2: 9, 3: 10, 16: 20, 17: 21}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (9,10,11) --> 9 - 11: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [9, 10, 11]
    assert all(s in splits for s in expected_splits)
    # 5 - 8 --> 12 - 15: Edge (unchanged)
    medge = single(minimizer.kcfg.merged_edges(source_id=5))
    assert medge.target.id == 12
    for i in range(6, 9):
        edge = single(minimizer.kcfg.edges(source_id=i))
        assert edge.target.id == i + 7


def check_merged_partial_one2(minimizer: KCFGMinimizer) -> None:
    minimizer.merge_nodes()
    # merged 9 - 12, else unchanged
    # 1 --> merged ai (2,3,4,5) & 6 - 8: Split
    split = single(minimizer.kcfg.splits(source_id=1))
    splits = split.splits
    expected_splits = [6, 7, 8, 24]
    assert all(s in splits for s in expected_splits)
    # merged ai (2,3,4,5) --> merged bi (9,10,11,12): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=24))
    edges = {2: 9, 3: 10, 16: 20, 17: 21, 18: 22, 19: 23}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (9,10,11,12) --> 9 - 12: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [9, 10, 11, 12]
    assert all(s in splits for s in expected_splits)
    # 6 - 8 --> 13 - 15: Edge (unchanged)
    for i in range(6, 9):
        edge = single(minimizer.kcfg.edges(source_id=i))
        assert edge.target.id == i + 7


def check_merged_two0(minimizer: KCFGMinimizer) -> None:
    minimizer.merge_nodes()
    # merged 9 - 10, 11 - 15, else unchanged
    # 1 --> merged ai (2,3) & (4-8): Split
    split = single(minimizer.kcfg.splits(source_id=1))
    splits = split.splits
    expected_splits = [24, 26]
    assert all(s in splits for s in expected_splits)
    # merged ai (4-8) --> merged bi (11-15): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=24))
    edges = {16: 20, 17: 21, 18: 22, 19: 23, 6: 13, 7: 14, 8: 15}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (11-15) --> 11 - 15: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [11, 12, 13, 14, 15]
    assert all(s in splits for s in expected_splits)
    # merged ai (2,3) --> merged bi (9,10): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=26))
    edges = {2: 9, 3: 10}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (9,10) --> 9 - 10: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [9, 10]
    assert all(s in splits for s in expected_splits)


def check_merged_two1(minimizer: KCFGMinimizer) -> None:
    minimizer.merge_nodes()
    # merged 9 - 11, 12 - 15, else unchanged
    # 1 --> merged ai (2,3,4) & (5-8): Split
    split = single(minimizer.kcfg.splits(source_id=1))
    splits = split.splits
    expected_splits = [24, 26]
    assert all(s in splits for s in expected_splits)
    # merged ai (5-8) --> merged bi (12-15): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=24))
    edges = {18: 22, 19: 23, 6: 13, 7: 14, 8: 15}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (12-15) --> 12 - 15: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [12, 13, 14, 15]
    assert all(s in splits for s in expected_splits)
    # merged ai (2,3,4) --> merged bi (9,10,11): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=26))
    edges = {2: 9, 3: 10, 16: 20, 17: 21}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (9,10,11) --> 9 - 11: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [9, 10, 11]
    assert all(s in splits for s in expected_splits)


def check_merged_partial_two(minimizer: KCFGMinimizer) -> None:
    minimizer.merge_nodes()
    # 1 --> merged ai (2,3,4) & (5,6) & 7 - 8: Split
    split = single(minimizer.kcfg.splits(source_id=1))
    splits = split.splits
    expected_splits = [7, 8, 24, 26]
    assert all(s in splits for s in expected_splits)
    # merged ai (5,6) --> merged bi (13,14): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=24))
    edges = {18: 22, 19: 23, 6: 13}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (13,14) --> 13 - 14: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [12, 13]
    assert all(s in splits for s in expected_splits)
    # merged ai (2,3,4) --> merged bi (9,10,11): MergedEdge
    merged_edge = single(minimizer.kcfg.merged_edges(source_id=26))
    edges = {2: 9, 3: 10, 16: 20, 17: 21}
    assert all(e.source.id in edges and e.target.id == edges[e.source.id] for e in merged_edge.edges)
    # merged bi (9,10,11) --> 9 - 11: Split
    split = single(minimizer.kcfg.splits(source_id=merged_edge.target.id))
    splits = split.splits
    expected_splits = [9, 10, 11]
    assert all(s in splits for s in expected_splits)


def check_merged_fail(minimizer: KCFGMinimizer) -> None:
    try:
        minimizer.merge_nodes()
        raise AssertionError
    except ValueError:
        pass


KCFG_MERGE_NODE_TEST_DATA: Final = (
    (MergedNo(), merge_node_test_kcfg(), check_merge_no),
    (MergedOne(), merge_node_test_kcfg(), check_merged_one),
    (MergedPartialOne0(), merge_node_test_kcfg(), check_merged_partial_one0),
    (MergedPartialOne1(), merge_node_test_kcfg(), check_merged_partial_one1),
    (MergedPartialOne2(), merge_node_test_kcfg(), check_merged_partial_one2),
    (MergedTwo0(), merge_node_test_kcfg(), check_merged_two0),
    (MergedTwo1(), merge_node_test_kcfg(), check_merged_two1),
    (MergedPartialTwo(), merge_node_test_kcfg(), check_merged_partial_two),
    (MergedFail(), merge_node_test_kcfg(), check_merged_fail),
)
