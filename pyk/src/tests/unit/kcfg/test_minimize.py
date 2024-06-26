from collections.abc import Callable

import pytest

from pyk.kast.inner import KVariable
from pyk.kcfg import KCFG
from pyk.kcfg.minimize import LiftEdgeEdge, LiftEdgeSplit
from pyk.kcfg.rewriter import KCFGRewriteWalker, KCFGRewritePattern
from pyk.prelude.kint import geInt, intToken, ltInt
from pyk.prelude.ml import mlEqualsTrue
from ..test_kcfg import minimization_test_kcfg, node_dicts, x_config, edge_dicts, split_dicts, \
    propagate_split_constraints, x_subst


# ------------------------------
# Test Helpers
# ------------------------------
def pop_nodes_by_ids(kcfg_dict: dict, node_ids: set[int]) -> dict:
    nodes = kcfg_dict['nodes']
    kcfg_dict['nodes'] = [node for node in nodes if node['id'] not in node_ids]
    return kcfg_dict


# ------------------------------
# Test Datas
# ------------------------------
def kcfg_two_splits_lifted_edge_edge() -> KCFG:
    #                              25   /-- X >=Int 5 --> 10
    #     50   /-- X >=Int 0 --> 6 --> 8
    #  1 --> 5                         \-- X  <Int 5 --> 11
    #         \                    105
    #          \-- X  <Int 0 --> 7 --> 13

    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
    x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))
    x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))

    d = {
        'next': 14,
        'nodes': node_dicts(13, config=x_config()),
        'edges': edge_dicts(
            (1, 5, 50, ('r1', 'r2', 'r3', 'r4')),
            (6, 8, 25, ('r5',)),
            (7, 13, 105, ('r6', 'r7', 'r8')),
        ),
        'splits': split_dicts((5, [(6, x_ge_0), (7, x_lt_0)]), (8, [(10, x_ge_5), (11, x_lt_5)]), csubst=x_subst()),
    }
    d = pop_nodes_by_ids(d, {2, 3, 4, 9, 12})
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    return cfg


def kcfg_two_splits_lifted_edge_edge_lifted_edge_split() -> KCFG:
    #                                                  50          25
    #                      /-- X >=Int 5 --> 1** (17) --> 6* (19) --> 10
    #  /-- X >=Int 0 --> 1* (15)                     50          25
    # 1                   \-- X <Int 5 --> 1** (18) --> 6* (20) --> 11
    # \                           50    105
    #  \-- X  <Int 0 --> 1* (16) --> 7 --> 13

    # todo: I don't implement this structure for now

    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
    x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))
    x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))

    d = {
        'next': 21,
        'nodes': node_dicts(20, config=x_config()),
        'edges': edge_dicts(
            (17, 19, 50, ('r1', 'r2', 'r3', 'r4')),
            (18, 20, 50, ('r1', 'r2', 'r3', 'r4')),
            (19, 10, 25, ('r5',)),
            (20, 11, 25, ('r5',)),
            (16, 7, 50, ('r1', 'r2', 'r3', 'r4')),
            (7, 13, 105, ('r6', 'r7', 'r8')),
        ),
        'splits': split_dicts((1, [(15, x_ge_0), (16, x_lt_0)]), (15, [(17, x_ge_5), (18, x_lt_5)]), csubst=x_subst()),
    }
    d = pop_nodes_by_ids(d, {2, 3, 4, 5, 8, 9, 12})
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    return cfg


 # todo: lifted edge-split
 #                                            5       10      15      20     25
 #                     /-- X >=Int 5 --> 1** --> 2** --> 3** --> 4** --> 6* --> 10
 #  /-- X >=Int 0 --> 1*                      5       10      15      20     25
 # 1                   \-- X  <Int 5 --> 1** --> 2** --> 3** --> 4** --> 6* --> 11
 #  \              5      10     15     20     25    30    35     40
 #   \-- X <Int 0 --> 1* --> 2* --> 3* --> 4* --> 7 --> 9 --> 12 --> 13


TWO_SPLITS = minimization_test_kcfg()
TWO_SPLITS_LIFTED_EDGE_EDGE = kcfg_two_splits_lifted_edge_edge()
TWO_SPLITS_LEE_LES = kcfg_two_splits_lifted_edge_edge_lifted_edge_split()


# ------------------------------
# Test Specifications
# ------------------------------
def assert_no_edge_edge(kcfg: KCFG):
    # no A->B->C
    for node in kcfg.nodes:
        assert not (kcfg.edges(source_id=node.id) and kcfg.edges(target_id=node.id))


def assert_no_edge_split(kcfg: KCFG):
    # no A->B->C*
    for node in kcfg.nodes:
        assert not (kcfg.edges(source_id=node.id) and kcfg.splits(target_id=node.id))


# ------------------------------
# Test Cases
# ------------------------------
@pytest.mark.parametrize("patterns, input_kcfg, assertions, expected_kcfg", [
    # ([LiftEdgeEdge()], TWO_SPLITS, [assert_no_edge_edge], TWO_SPLITS_LIFTED_EDGE_EDGE),
    ([LiftEdgeSplit()], TWO_SPLITS_LIFTED_EDGE_EDGE, [assert_no_edge_split], TWO_SPLITS_LEE_LES),
])
def test_minimize_patterns(
        patterns: list[KCFGRewritePattern],
        input_kcfg: KCFG,
        assertions: list[Callable[[KCFG], None]],
        expected_kcfg: KCFG):
    walker = KCFGRewriteWalker(patterns)
    walker.rewrite(input_kcfg)
    for assertion in assertions:
        assertion(input_kcfg)
    if expected_kcfg:
        assert input_kcfg.to_dict() == expected_kcfg.to_dict()
