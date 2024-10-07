from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KVariable
from pyk.kcfg import KCFG, KCFGShow
from pyk.kcfg.minimize import KCFGMinimizer
from pyk.kcfg.show import NodePrinter
from pyk.prelude.kint import geInt, intToken, ltInt
from pyk.prelude.ml import mlEqualsTrue, mlTop
from pyk.utils import single

from ..kcfg.merge_node_data import KCFG_MERGE_NODE_TEST_DATA
from ..mock_kprint import MockKPrint
from ..test_kcfg import edge_dicts, node_dicts, split_dicts, to_csubst_node, x_config, x_node, x_subst

if TYPE_CHECKING:
    from collections.abc import Callable

    from pyk.kast.inner import KApply
    from pyk.kcfg.kcfg import NodeIdLike
    from pyk.kcfg.semantics import KCFGSemantics


def contains_edge(cfg: KCFG, source: NodeIdLike, target: NodeIdLike, depth: int, rules: tuple[str, ...]) -> bool:
    edges = cfg.edges(source_id=source, target_id=target)
    if edges:
        edge = single(edges)
        return edge.depth == depth and edge.rules == rules
    return False


def propagate_split_constraints(cfg: KCFG) -> None:
    for split in cfg.splits():
        for target, csubst in split._targets:
            if csubst.constraint != mlTop():
                for target_successor in cfg.reachable_nodes(target.id):
                    new_node = KCFG.Node(target_successor.id, target_successor.cterm.add_constraint(csubst.constraint))
                    cfg.replace_node(new_node)


def minimization_test_kcfg() -> KCFG:
    #                                               25   /-- X >=Int 5 --> 10
    #     5    10    15    20   /-- X >=Int 0 --> 6 --> 8
    #  1 --> 2 --> 3 --> 4 --> 5                         \-- X  <Int 5 --> 11
    #                           \                    30    35     40
    #                            \-- X  <Int 0 --> 7 --> 9 --> 12 --> 13

    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
    x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))
    x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))

    d = {
        'next': 14,
        'nodes': node_dicts(13, config=x_config()),
        'edges': edge_dicts(
            (1, 2, 5, ('r1',)),
            (2, 3, 10, ('r2',)),
            (3, 4, 15, ('r3',)),
            (4, 5, 20, ('r4',)),
            (6, 8, 25, ('r5',)),
            (7, 9, 30, ('r6',)),
            (9, 12, 35, ('r7',)),
            (12, 13, 40, ('r8',)),
        ),
        'splits': split_dicts((5, [(6, x_ge_0), (7, x_lt_0)]), (8, [(10, x_ge_5), (11, x_lt_5)]), csubst=x_subst()),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    return cfg


def test_lifting_functions_manual() -> None:
    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
    x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))
    x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))
    y_ge_0 = mlEqualsTrue(geInt(KVariable('Y'), intToken(0)))
    y_lt_0 = mlEqualsTrue(ltInt(KVariable('Y'), intToken(0)))

    d = {
        'next': 13,
        'nodes': node_dicts(12, config=x_config()),
        'edges': edge_dicts(
            (1, 2, 25, ('r1',)),
            (2, 3, 30, ('r2',)),
            (4, 6, 10, ('r3',)),
            (5, 7, 20, ('r4',)),
            (7, 10, 15, ('r5',)),
        ),
        'splits': split_dicts(
            (3, [(4, x_ge_0), (5, x_lt_0)]),
            (6, [(8, y_ge_0), (9, y_lt_0)]),
            (9, [(11, x_ge_5), (12, x_lt_5)]),
            csubst=x_subst(),
        ),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    #                                   10   /-- Y >=Int 0 -- 8
    #    25    30   /-- X >=Int 0 --> 4 --> 6                  /-- X >=Int 5 --> 11
    #  1 --> 2 --> 3                         \-- Y  <Int 0 -- 9
    #               \                   20    15               \-- X <=Int 5 --> 12
    #                \-- X <Int 0 --> 5 --> 7 --> 10

    minimizer = KCFGMinimizer(cfg)

    for id in [1, 3, 4, 5, 6, 8, 9, 10, 11, 12]:
        with pytest.raises(ValueError, match='^Expected a single element, found none$'):
            minimizer.lift_edge(id)

    for id in [1, 2, 4, 5, 7, 8, 9, 10, 11, 12]:
        with pytest.raises(ValueError, match='^Expected a single element, found none$'):
            minimizer.lift_split_edge(id)
    with pytest.raises(AssertionError):
        minimizer.lift_split_edge(6)

    for id in [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]:
        with pytest.raises(ValueError, match='^Expected a single element, found none$'):
            minimizer.lift_split_split(id)

    minimizer.lift_edge(2)
    minimizer.lift_edge(7)
    assert cfg._deleted_nodes == {2, 7}
    assert contains_edge(cfg, 1, 3, 55, ('r1', 'r2'))
    assert contains_edge(cfg, 5, 10, 35, ('r4', 'r5'))

    minimizer.lift_split_edge(3)
    assert cfg._deleted_nodes == {2, 3, 7}

    node_13 = KCFG.Node(13, x_node(1).cterm.add_constraint(x_ge_0))
    node_14 = KCFG.Node(14, x_node(1).cterm.add_constraint(x_lt_0))
    assert cfg.node(13) == node_13
    assert cfg.node(14) == node_14
    assert cfg._node_id == 15

    assert contains_edge(cfg, 13, 4, 55, ('r1', 'r2'))
    assert contains_edge(cfg, 14, 5, 55, ('r1', 'r2'))
    assert cfg.contains_split(
        KCFG.Split(
            x_node(1),
            [
                (node_13, to_csubst_node(x_node(1), node_13, [x_ge_0])),
                (node_14, to_csubst_node(x_node(1), node_14, [x_lt_0])),
            ],
        )
    )

    with pytest.raises(AssertionError):
        minimizer.lift_split_split(9)

    minimizer.lift_edge(4)
    minimizer.lift_edge(5)
    assert not minimizer.lift_edges()
    assert not minimizer.lift_splits()


def test_lifting_functions_automatic() -> None:
    cfg = minimization_test_kcfg()
    minimizer = KCFGMinimizer(cfg)

    minimizer.lift_edges()
    #                                  /-- X >=Int 5 --> 20
    #    50   /-- X >=Int 0 --> 6 --> 8
    #  1 --> 5                         \-- X  <Int 5 --> 21
    #         \                   105
    #          \-- X <Int 0 --> 7 --> 13
    assert cfg._deleted_nodes == {2, 3, 4, 9, 12}

    assert contains_edge(cfg, 1, 5, 50, ('r1', 'r2', 'r3', 'r4'))
    assert contains_edge(cfg, 7, 13, 105, ('r6', 'r7', 'r8'))

    minimizer.lift_splits()
    #                                    50     25
    #    /-- X >=Int 0, X >=Int 5 --> 18 --> 16 --> 10
    #   /                              50     25
    #  1 -- X >=Int 0, X <Int 5 --> 19 --> 17 --> 11
    #   \                    50    105
    #    \-- X <Int 0 --> 15 --> 7 --> 13
    assert cfg._deleted_nodes == {2, 3, 4, 5, 6, 8, 9, 12, 14}

    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
    x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))
    x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))
    node_14 = KCFG.Node(14, x_node(14).cterm.add_constraint(x_ge_0))
    node_15 = KCFG.Node(15, x_node(15).cterm.add_constraint(x_lt_0))
    node_16 = KCFG.Node(16, x_node(16).cterm.add_constraint(x_ge_0).add_constraint(x_ge_5))
    node_17 = KCFG.Node(17, x_node(17).cterm.add_constraint(x_ge_0).add_constraint(x_lt_5))
    node_18 = KCFG.Node(18, node_14.cterm.add_constraint(x_ge_5))
    node_19 = KCFG.Node(19, node_14.cterm.add_constraint(x_lt_5))
    assert cfg.node(15) == node_15
    assert cfg.node(16) == node_16
    assert cfg.node(17) == node_17
    assert cfg.node(18) == node_18
    assert cfg.node(19) == node_19
    assert cfg._node_id == 20

    assert cfg.contains_split(
        KCFG.Split(
            x_node(1),
            [
                (node_15, to_csubst_node(x_node(1), node_19, [x_lt_0])),
                (node_18, to_csubst_node(x_node(1), node_18, [x_ge_0, x_ge_5])),
                (node_19, to_csubst_node(x_node(1), node_19, [x_lt_5, x_ge_0])),
            ],
        )
    )
    assert contains_edge(cfg, 18, 16, 50, ('r1', 'r2', 'r3', 'r4'))
    assert contains_edge(cfg, 16, 10, 25, ('r5',))
    assert contains_edge(cfg, 19, 17, 50, ('r1', 'r2', 'r3', 'r4'))
    assert contains_edge(cfg, 17, 11, 25, ('r5',))
    assert contains_edge(cfg, 15, 7, 50, ('r1', 'r2', 'r3', 'r4'))


def test_minimize_01() -> None:
    cfg = minimization_test_kcfg()
    minimizer = KCFGMinimizer(cfg)

    minimizer.minimize()
    #                                    75
    #    /-- X >=Int 0, X >=Int 5 --> 18 --> 10
    #   /                              75
    #  1 -- X >=Int 0, X <Int 5 --> 19 --> 11
    #   \                    155
    #    \-- X <Int 0 --> 15 --> 13
    assert cfg._deleted_nodes == {2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 16, 17}

    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
    x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))
    x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))
    node_14 = KCFG.Node(14, x_node(1).cterm.add_constraint(x_ge_0))
    node_15 = KCFG.Node(15, x_node(1).cterm.add_constraint(x_lt_0))
    node_18 = KCFG.Node(18, node_14.cterm.add_constraint(x_ge_5))
    node_19 = KCFG.Node(19, node_14.cterm.add_constraint(x_lt_5))
    assert cfg.node(15) == node_15
    assert cfg.node(18) == node_18
    assert cfg.node(19) == node_19
    assert cfg._node_id == 20

    assert cfg.contains_split(
        KCFG.Split(
            x_node(1),
            [
                (node_15, to_csubst_node(x_node(1), node_19, [x_lt_0])),
                (node_18, to_csubst_node(x_node(1), node_18, [x_ge_0, x_ge_5])),
                (node_19, to_csubst_node(x_node(1), node_19, [x_lt_5, x_ge_0])),
            ],
        )
    )
    assert contains_edge(cfg, 18, 10, 75, ('r1', 'r2', 'r3', 'r4', 'r5'))
    assert contains_edge(cfg, 19, 11, 75, ('r1', 'r2', 'r3', 'r4', 'r5'))
    assert contains_edge(cfg, 15, 13, 155, ('r1', 'r2', 'r3', 'r4', 'r6', 'r7', 'r8'))


def test_minimize_02() -> None:
    x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
    x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))

    d = {
        'next': 7,
        'nodes': node_dicts(6, config=x_config()),
        'edges': edge_dicts(
            (1, 2, 10, ('r1',)),
            (3, 5, 20, ('r2',)),
            (4, 6, 30, ('r3',)),
        ),
        'splits': split_dicts(
            (2, [(3, x_ge_0), (4, x_lt_0)]),
            csubst=x_subst(),
        ),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    minimizer = KCFGMinimizer(cfg)
    #                             20
    #    10   /-- X >=Int 0 --> 3 --> 5
    #  1 --> 2                    30
    #         \-- X  <Int 0 --> 4 --> 6

    minimizer.minimize()
    #                       30
    #   /-- X >=Int 0 --> 7 --> 5
    #  1                    40
    #   \-- X  <Int 0 --> 8 --> 6

    assert cfg._deleted_nodes == {2, 3, 4}

    node_7 = KCFG.Node(7, x_node(1).cterm.add_constraint(x_ge_0))
    node_8 = KCFG.Node(8, x_node(1).cterm.add_constraint(x_lt_0))
    assert cfg.node(7) == node_7
    assert cfg.node(8) == node_8
    assert cfg._node_id == 9

    assert cfg.contains_split(
        KCFG.Split(
            x_node(1),
            [
                (node_7, to_csubst_node(x_node(1), node_7, [x_ge_0])),
                (node_8, to_csubst_node(x_node(1), node_8, [x_lt_0])),
            ],
        )
    )
    assert contains_edge(cfg, 7, 5, 30, ('r1', 'r2'))
    assert contains_edge(cfg, 8, 6, 40, ('r1', 'r3'))


def test_split_constraint_accumulation() -> None:
    def x_ge(n: int) -> KApply:
        return mlEqualsTrue(geInt(KVariable('X'), intToken(n)))

    def x_lt(n: int) -> KApply:
        return mlEqualsTrue(ltInt(KVariable('X'), intToken(n)))

    d = {
        'next': 16,
        'nodes': node_dicts(15, config=x_config()),
        'edges': edge_dicts(),
        'splits': split_dicts(
            (1, [(2, x_ge(0)), (3, x_lt(0))]),
            (2, [(4, x_ge(32)), (5, x_lt(32))]),
            (3, [(6, x_ge(-32)), (7, x_lt(-32))]),
            (4, [(8, x_ge(64)), (9, x_lt(64))]),
            (5, [(10, x_ge(16)), (11, x_lt(16))]),
            (6, [(12, x_ge(-16)), (13, x_lt(-16))]),
            (7, [(14, x_ge(-64)), (15, x_lt(-64))]),
            csubst=x_subst(),
        ),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    minimizer = KCFGMinimizer(cfg)

    minimizer.minimize()

    kcfg_show = KCFGShow(MockKPrint(), node_printer=NodePrinter(MockKPrint()))
    actual = '\n'.join(kcfg_show.pretty(cfg)) + '\n'

    expected = (
        '\n'
        '┌─ 1 (root, split)\n'
        '┃\n'
        '┃ (branch)\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , 32 )\n'
        '┃  ┃     _>=Int_ ( X , 64 )\n'
        '┃  │\n'
        '┃  └─ 8 (leaf)\n'
        '┃\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _<Int_ ( X , 64 )\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , 32 )\n'
        '┃  │\n'
        '┃  └─ 9 (leaf)\n'
        '┃\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _<Int_ ( X , 32 )\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , 16 )\n'
        '┃  │\n'
        '┃  └─ 10 (leaf)\n'
        '┃\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _<Int_ ( X , 16 )\n'
        '┃  ┃     _<Int_ ( X , 32 )\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  │\n'
        '┃  └─ 11 (leaf)\n'
        '┃\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _<Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , -16 )\n'
        '┃  ┃     _>=Int_ ( X , -32 )\n'
        '┃  │\n'
        '┃  └─ 12 (leaf)\n'
        '┃\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _<Int_ ( X , 0 )\n'
        '┃  ┃     _<Int_ ( X , -16 )\n'
        '┃  ┃     _>=Int_ ( X , -32 )\n'
        '┃  │\n'
        '┃  └─ 13 (leaf)\n'
        '┃\n'
        '┣━━┓ subst: .Subst\n'
        '┃  ┃ constraint:\n'
        '┃  ┃     _<Int_ ( X , 0 )\n'
        '┃  ┃     _<Int_ ( X , -32 )\n'
        '┃  ┃     _>=Int_ ( X , -64 )\n'
        '┃  │\n'
        '┃  └─ 14 (leaf)\n'
        '┃\n'
        '┗━━┓ subst: .Subst\n'
        '   ┃ constraint:\n'
        '   ┃     _<Int_ ( X , 0 )\n'
        '   ┃     _<Int_ ( X , -32 )\n'
        '   ┃     _<Int_ ( X , -64 )\n'
        '   │\n'
        '   └─ 15 (leaf)\n'
        '\n'
    )

    assert actual == expected


@pytest.mark.parametrize('heuristics,kcfg,check', KCFG_MERGE_NODE_TEST_DATA)
def test_merge_nodes(heuristics: KCFGSemantics, kcfg: KCFG, check: Callable[[KCFGMinimizer], None]) -> None:
    # When
    minimizer = KCFGMinimizer(kcfg, heuristics)

    # Then
    check(minimizer)
