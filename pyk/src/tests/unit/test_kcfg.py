from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CSubst, CTerm
from pyk.kast.inner import KApply, KRewrite, KToken, KVariable, Subst
from pyk.kast.manip import no_cell_rewrite_to_dots
from pyk.kcfg import KCFG, KCFGShow
from pyk.kcfg.kcfg import KCFGNodeAttr
from pyk.kcfg.show import NodePrinter
from pyk.prelude.kint import geInt, intToken, ltInt
from pyk.prelude.ml import mlEquals, mlEqualsTrue, mlTop
from pyk.prelude.utils import token
from pyk.utils import not_none, single

from .mock_kprint import MockKPrint

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Any

    from pyk.kast import KInner
    from pyk.kcfg.kcfg import NodeIdLike


def to_csubst_cterm(term_1: CTerm, term_2: CTerm, constraints: Iterable[KInner]) -> CSubst:
    csubst = term_1.match_with_constraint(term_2)
    assert csubst is not None
    for constraint in constraints:
        csubst = csubst.add_constraint(constraint)
    return csubst


def to_csubst_node(node_1: KCFG.Node, node_2: KCFG.Node, constraints: Iterable[KInner]) -> CSubst:
    return to_csubst_cterm(node_1.cterm, node_2.cterm, constraints)


def to_csubst_id(source_id: int, target_id: int, constraints: Iterable[KInner]) -> CSubst:
    return to_csubst_cterm(term(source_id), term(target_id), constraints)


def x_equals(i: int) -> KInner:
    return mlEquals(KVariable('X'), token(i))


def x_config() -> KInner:
    return KApply('<top>', KVariable('X'))


def x_subst() -> CSubst:
    return CSubst(Subst({'X': KVariable('X')}))


def x_node(i: int) -> KCFG.Node:
    return node(i, config=x_config())


# over 10 is variables
def term(i: int, auto_cond: bool = False, config: KInner | None = None) -> CTerm:
    if config is None:
        inside: KInner = token(i)
        if i > 10:
            inside = KVariable('V' + str(i))
        config = KApply('<top>', [inside])
    cond = (x_equals(i),) if auto_cond else ()
    return CTerm(not_none(config), cond)


def node(i: int, auto_cond: bool = False, config: KInner | None = None) -> KCFG.Node:
    return KCFG.Node(i, term(i, auto_cond, config))


def edge(i: int, j: int) -> KCFG.Edge:
    return KCFG.Edge(node(i), node(j), (1,), ((),), (CSubst(),))


def cover(i: int, j: int) -> KCFG.Cover:
    csubst = term(j).match_with_constraint(term(i))
    assert csubst is not None
    return KCFG.Cover(node(i), node(j), csubst)


def split(i: int, js: Iterable[int], config: KInner | None = None) -> KCFG.Split:
    split_substs = []
    for j in js:
        csubst = term(i, config=config).match_with_constraint(term(j, config=config))
        assert csubst is not None
        split_substs.append(csubst)
    return KCFG.Split(node(i, config=config), zip((node(j, config=config) for j in js), split_substs, strict=True))


def ndbranch(i: int, js: Iterable[int]) -> KCFG.NDBranch:
    return KCFG.NDBranch(node(i), tuple(node(j) for j in js), ())


def node_dicts(n: int, start: int = 1, auto_cond: bool = False, config: KInner | None = None) -> list[dict[str, Any]]:
    return [node(i, auto_cond, config).to_dict() for i in range(start, start + n)]


def edge_dicts(*edges: Iterable) -> list[dict[str, Any]]:
    def _make_edge_dict(i: int, j: int, depth: int = 1, rules: tuple[str, ...] = ()) -> dict[str, Any]:
        return {
            'source': i,
            'target': j,
            'depths': [depth],
            'rules_list': [list(rules)],
            'csubsts': [CSubst().to_dict()],
        }

    return [_make_edge_dict(*edge) for edge in edges]


def cover_dicts(*edges: tuple[int, int]) -> list[dict[str, Any]]:
    covers = []
    for i, j in edges:
        csubst = term(j).match_with_constraint(term(i))
        assert csubst is not None
        covers.append({'source': i, 'target': j, 'csubst': csubst.to_dict()})
    return covers


def split_dicts(*edges: tuple[int, Iterable[tuple[int, KInner]]], csubst: CSubst | None = None) -> list[dict[str, Any]]:
    return [
        {
            'source': source_id,
            'targets': [
                {
                    'target': target_id,
                    'csubst': (
                        to_csubst_id(source_id, target_id, [constraint]).to_dict()
                        if csubst is None
                        else csubst.add_constraint(constraint).to_dict()
                    ),
                }
                for target_id, constraint in targets
            ],
        }
        for source_id, targets in edges
    ]


def ndbranch_dicts(*edges: tuple[int, Iterable[tuple[int, bool]]]) -> list[dict[str, Any]]:
    return [
        {
            'source': source_id,
            'targets': [target_id for target_id, _ in target_ids],
            'rules': [],
        }
        for source_id, target_ids in edges
    ]


def test_from_dict_single_node() -> None:
    # Given
    d = {'next': 2, 'nodes': node_dicts(1)}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(1)}
    assert cfg.to_dict() == d


def test_from_dict_two_nodes() -> None:
    # Given
    d = {'next': 3, 'nodes': node_dicts(2)}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(1), node(2)}
    assert cfg.to_dict() == d


def test_from_dict_loop_edge() -> None:
    # Given
    d = {'next': 3, 'nodes': node_dicts(2), 'edges': edge_dicts((1, 2), (2, 1))}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(1), node(2)}
    assert set(cfg.edges()) == {edge(1, 2), edge(2, 1)}
    assert cfg.edge(1, 2) == edge(1, 2)
    assert cfg.edge(2, 1) == edge(2, 1)
    assert cfg.to_dict() == d


def test_from_dict_simple_edge() -> None:
    # Given
    d = {'nodes': node_dicts(2), 'edges': edge_dicts((1, 2))}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(1), node(2)}
    assert set(cfg.edges()) == {edge(1, 2)}
    assert cfg.edge(1, 2) == edge(1, 2)


def test_to_dict() -> None:
    # Given
    d = {'nodes': node_dicts(2), 'edges': edge_dicts((1, 2)), 'next': 3}

    # When
    cfg = KCFG.from_dict(d)
    cfg_dict = cfg.to_dict()

    # Then
    assert cfg_dict == d


def test_to_dict_repeated() -> None:
    # Given
    d = {'nodes': node_dicts(2), 'edges': edge_dicts((1, 2)), 'next': 3}

    # When
    cfg = KCFG.from_dict(d)
    cfg_dict1 = cfg.to_dict()
    cfg_dict2 = cfg.to_dict()

    # Then
    assert cfg_dict1 == cfg_dict2


def test_create_node() -> None:
    # Given
    cfg = KCFG()

    # When
    new_node = cfg.create_node(term(1))

    # Then
    assert new_node == node(1)
    assert set(cfg.nodes) == {node(1)}
    assert not cfg.is_stuck(new_node.id)


def test_remove_unknown_node() -> None:
    # Given
    cfg = KCFG()

    # Then
    with pytest.raises(ValueError):
        # When
        cfg.remove_node(0)


def test_remove_node() -> None:
    # Given
    d = {'nodes': node_dicts(3), 'edges': edge_dicts((1, 2), (2, 3))}
    cfg = KCFG.from_dict(d)

    # When
    cfg.remove_node(2)

    # Then
    assert set(cfg.nodes) == {node(1), node(3)}
    assert set(cfg.edges()) == set()
    assert not cfg.is_stuck(1)
    with pytest.raises(ValueError):
        cfg.node(2)
    with pytest.raises(ValueError):
        cfg.edge(1, 2)
    with pytest.raises(ValueError):
        cfg.edge(2, 3)


def test_cover_then_remove() -> None:
    # Given
    cfg = KCFG()

    # When
    node1 = cfg.create_node(CTerm(KApply('<top>', token(1))))
    node2 = cfg.create_node(CTerm(KApply('<top>', KVariable('X'))))
    cover = cfg.create_cover(node1.id, node2.id)

    # Then
    assert cfg.is_covered(node1.id)
    assert not cfg.is_covered(node2.id)
    assert dict(cover.csubst.subst) == {'X': token(1)}
    assert cfg.covers() == [cover]

    # When
    cfg.remove_cover(node1.id, node2.id)

    # Then
    assert not cfg.is_covered(node1.id)
    assert not cfg.is_covered(node2.id)
    assert cfg.covers() == []


def test_insert_simple_edge() -> None:
    # Given
    d = {'nodes': node_dicts(2)}
    cfg = KCFG.from_dict(d)

    # When
    new_edge = cfg.create_edge(1, 2, 1)

    # Then
    assert new_edge == edge(1, 2)
    assert set(cfg.nodes) == {node(1), node(2)}
    assert set(cfg.edges()) == {edge(1, 2)}


def test_get_successors() -> None:
    d = {
        'next': 19,
        'nodes': node_dicts(18),
        'edges': edge_dicts((11, 12)),
        'splits': split_dicts((12, [(13, mlTop()), (14, mlTop())])),
        'covers': cover_dicts((14, 11)),
        'ndbranches': ndbranch_dicts((13, [(16, False), (17, False)])),
    }
    cfg = KCFG.from_dict(d)

    # When
    edges = set(cfg.edges(source_id=11))
    covers = set(cfg.covers(source_id=14))
    splits = sorted(cfg.splits(source_id=12))
    ndbranches = set(cfg.ndbranches(source_id=13))

    # Then
    assert edges == {edge(11, 12)}
    assert covers == {cover(14, 11)}
    assert splits == [split(12, [13, 14])]
    assert ndbranches == {ndbranch(13, [16, 17])}
    assert cfg.to_dict() == d


def test_get_predecessors() -> None:
    d = {'nodes': node_dicts(3), 'edges': edge_dicts((1, 3), (2, 3))}
    cfg = KCFG.from_dict(d)

    # When
    preds = set(cfg.edges(target_id=3))

    # Then
    assert preds == {edge(1, 3), edge(2, 3)}


def test_reachable_nodes() -> None:
    # Given
    d = {
        'nodes': node_dicts(20),
        'edges': edge_dicts((13, 15), (14, 15), (15, 12)),
        'covers': cover_dicts((12, 13)),
        'splits': split_dicts(
            (16, [(12, mlTop()), (13, mlTop()), (17, mlTop())]), (17, [(12, mlTop()), (18, mlTop())])
        ),
        'ndbranches': ndbranch_dicts((18, [(19, False), (20, False)])),
    }
    cfg = KCFG.from_dict(d)

    # When
    nodes_2 = cfg.reachable_nodes(12)
    nodes_3 = cfg.reachable_nodes(16)
    nodes_4 = cfg.reachable_nodes(13, reverse=True)
    nodes_5 = cfg.reachable_nodes(19, reverse=True)

    # Then
    assert nodes_2 == {node(12), node(13), node(15)}
    assert nodes_3 == {node(16), node(12), node(13), node(17), node(18), node(15), node(19), node(20)}
    assert nodes_4 == {node(13), node(16), node(12), node(15), node(17), node(14)}
    assert nodes_5 == {node(19), node(18), node(17), node(16)}


def test_paths_between() -> None:
    # Given
    d = {
        'nodes': node_dicts(20),
        'edges': edge_dicts((13, 15), (14, 15), (15, 12)),
        'covers': cover_dicts((12, 13)),
        'splits': split_dicts(
            (16, [(12, mlTop()), (13, mlTop()), (17, mlTop())]), (17, [(12, mlTop()), (18, mlTop())])
        ),
        'ndbranches': ndbranch_dicts((18, [(19, False), (20, False)])),
    }
    cfg = KCFG.from_dict(d)

    # When
    paths = sorted(cfg.paths_between(16, 15))

    # Then
    assert paths == [
        (split(16, [12]), cover(12, 13), edge(13, 15)),
        (split(16, [13]), edge(13, 15)),
        (split(16, [17]), split(17, [12]), cover(12, 13), edge(13, 15)),
    ]

    # When
    paths = sorted(cfg.paths_between(17, 20))

    # Then
    assert paths == [
        (split(17, [18]), ndbranch(18, [20])),
    ]


def test_resolve() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
    }
    cfg = KCFG.from_dict(d)

    assert node(1) == cfg.node(1)


def test_vacuous() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
        'edges': edge_dicts((1, 2), (2, 3)),
        'aliases': {'foo': 2},
    }

    cfg = KCFG.from_dict(d)
    cfg.add_vacuous(3)
    assert cfg.vacuous, node(3)


def test_let_node() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
        'edges': edge_dicts((1, 2), (2, 3)),
    }

    cfg = KCFG.from_dict(d)
    cfg.let_node(2, cterm=term(5))

    node = cfg.node(2)
    assert node is not None
    assert node.cterm == term(5)

    first_edge = cfg.edge(1, 2)
    assert first_edge is not None
    assert first_edge.target.cterm == term(5)

    second_edge = cfg.edge(2, 3)
    assert second_edge is not None
    assert second_edge.source.cterm == term(5)


def test_aliases() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
        'edges': edge_dicts((1, 2), (2, 3)),
        'aliases': {'foo': 2},
    }

    cfg = KCFG.from_dict(d)
    assert cfg.node('@foo'), node(2)

    cfg.add_alias('bar', 1)
    cfg.add_alias('bar2', 1)
    assert cfg.node('@bar'), node(1)
    assert cfg.node('@bar2'), node(1)
    cfg.remove_alias('bar')
    with pytest.raises(ValueError, match='Unknown alias: @bar'):
        cfg.node('@bar')

    with pytest.raises(ValueError, match='Duplicate alias: bar2'):
        cfg.add_alias('bar2', 2)
    with pytest.raises(ValueError, match='Alias may not contain "@"'):
        cfg.add_alias('@buzz', 2)
    with pytest.raises(ValueError, match='Unknown node: 10'):
        cfg.add_alias('buzz', 10)


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

    for id in [1, 3, 4, 5, 6, 8, 9, 10, 11, 12]:
        with pytest.raises(ValueError, match='^Expected a single element, found none$'):
            cfg.lift_edge(id)

    for id in [1, 2, 4, 5, 7, 8, 9, 10, 11, 12]:
        with pytest.raises(ValueError, match='^Expected a single element, found none$'):
            cfg.lift_split_edge(id)
    with pytest.raises(AssertionError):
        cfg.lift_split_edge(6)

    for id in [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]:
        with pytest.raises(ValueError, match='^Expected a single element, found none$'):
            cfg.lift_split_split(id)

    cfg.lift_edge(2)
    cfg.lift_edge(7)
    assert cfg._deleted_nodes == {2, 7}
    assert contains_edge(cfg, 1, 3, 55, ('r1', 'r2'))
    assert contains_edge(cfg, 5, 10, 35, ('r4', 'r5'))

    cfg.lift_split_edge(3)
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
        cfg.lift_split_split(9)

    cfg.lift_edge(4)
    cfg.lift_edge(5)
    assert not cfg.lift_edges()
    assert not cfg.lift_splits()


def test_lifting_functions_automatic() -> None:
    cfg = minimization_test_kcfg()

    cfg.lift_edges()
    #                                  /-- X >=Int 5 --> 20
    #    50   /-- X >=Int 0 --> 6 --> 8
    #  1 --> 5                         \-- X  <Int 5 --> 21
    #         \                   105
    #          \-- X <Int 0 --> 7 --> 13
    assert cfg._deleted_nodes == {2, 3, 4, 9, 12}

    assert contains_edge(cfg, 1, 5, 50, ('r1', 'r2', 'r3', 'r4'))
    assert contains_edge(cfg, 7, 13, 105, ('r6', 'r7', 'r8'))

    cfg.lift_splits()
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
                (node_19, to_csubst_node(x_node(1), node_19, [x_ge_0, x_lt_5])),
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

    cfg.minimize()
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
                (node_19, to_csubst_node(x_node(1), node_19, [x_ge_0, x_lt_5])),
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
    #                             20
    #    10   /-- X >=Int 0 --> 3 --> 5
    #  1 --> 2                    30
    #         \-- X  <Int 0 --> 4 --> 6

    cfg.minimize()
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

    cfg.minimize()

    kcfg_show = KCFGShow(MockKPrint(), node_printer=NodePrinter(MockKPrint()))
    actual = '\n'.join(kcfg_show.pretty(cfg)) + '\n'

    expected = (
        '\n'
        '┌─ 1 (root, split)\n'
        '┃\n'
        '┃ (branch)\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , 32 )\n'
        '┃  ┃     _>=Int_ ( X , 64 )\n'
        '┃  │\n'
        '┃  └─ 8 (leaf)\n'
        '┃\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , 32 )\n'
        '┃  ┃     _<Int_ ( X , 64 )\n'
        '┃  │\n'
        '┃  └─ 9 (leaf)\n'
        '┃\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _<Int_ ( X , 32 )\n'
        '┃  ┃     _>=Int_ ( X , 16 )\n'
        '┃  │\n'
        '┃  └─ 10 (leaf)\n'
        '┃\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _>=Int_ ( X , 0 )\n'
        '┃  ┃     _<Int_ ( X , 32 )\n'
        '┃  ┃     _<Int_ ( X , 16 )\n'
        '┃  │\n'
        '┃  └─ 11 (leaf)\n'
        '┃\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _<Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , -32 )\n'
        '┃  ┃     _>=Int_ ( X , -16 )\n'
        '┃  │\n'
        '┃  └─ 12 (leaf)\n'
        '┃\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _<Int_ ( X , 0 )\n'
        '┃  ┃     _>=Int_ ( X , -32 )\n'
        '┃  ┃     _<Int_ ( X , -16 )\n'
        '┃  │\n'
        '┃  └─ 13 (leaf)\n'
        '┃\n'
        '┣━━┓ constraints:\n'
        '┃  ┃     _<Int_ ( X , 0 )\n'
        '┃  ┃     _<Int_ ( X , -32 )\n'
        '┃  ┃     _>=Int_ ( X , -64 )\n'
        '┃  │\n'
        '┃  └─ 14 (leaf)\n'
        '┃\n'
        '┗━━┓ constraints:\n'
        '   ┃     _<Int_ ( X , 0 )\n'
        '   ┃     _<Int_ ( X , -32 )\n'
        '   ┃     _<Int_ ( X , -64 )\n'
        '   │\n'
        '   └─ 15 (leaf)\n'
        '\n'
    )

    assert actual == expected


def test_split_csubsts() -> None:
    cfg = KCFG()
    cfg.create_node(term(11))
    cfg.split_on_constraints(1, [x_equals(10), x_equals(20)])
    # The target substitutions are identities, with the appropriate constraints
    split = single(cfg.splits())
    assert split.source == KCFG.Node(1, term(11))
    assert split._targets[0][1] == CSubst(Subst({'V11': KVariable('V11')}), [x_equals(10)])
    assert split._targets[1][1] == CSubst(Subst({'V11': KVariable('V11')}), [x_equals(20)])


def test_write_cfg_data(tmp_path: Path) -> None:
    def _written_nodes() -> set[str]:
        return {nd_path.name for nd_path in (tmp_path / 'nodes').iterdir()}

    kcfg = KCFG(cfg_dir=tmp_path)

    kcfg.add_node(node(1))
    kcfg.add_node(node(2))
    kcfg.add_node(node(3))

    assert _written_nodes() == set()

    kcfg.write_cfg_data()

    assert _written_nodes() == {'1.json', '2.json', '3.json'}

    kcfg.add_node(node(4))
    kcfg.remove_node(1)
    kcfg.remove_node(2)
    kcfg.let_node(3, cterm=node(3).cterm)
    kcfg.add_node(node(2))

    assert _written_nodes() == {'1.json', '2.json', '3.json'}

    kcfg.write_cfg_data()

    assert _written_nodes() == {'2.json', '3.json', '4.json'}


def test_read_write_cfg_data(tmp_path: Path) -> None:

    kcfg = KCFG(cfg_dir=tmp_path)

    kcfg.add_node(node(1))
    kcfg.add_node(node(2))
    kcfg.add_node(node(3))
    kcfg.add_attr(1, KCFGNodeAttr.VACUOUS)
    kcfg.add_attr(2, KCFGNodeAttr.STUCK)

    kcfg.write_cfg_data()
    read_kcfg = KCFG.read_cfg_data(tmp_path)

    assert set(kcfg.nodes) == set(read_kcfg.nodes)


def test_pretty_print() -> None:
    nodes = node_dicts(15, start=10) + node_dicts(1, start=25, auto_cond=True)
    nodes_dict = {node['id']: node for node in nodes}
    nodes_dict[23]['attrs'] = [KCFGNodeAttr.STUCK.value]
    nodes_dict[17]['attrs'] = [KCFGNodeAttr.VACUOUS.value]
    nodes = list(nodes_dict.values())

    d = {
        'nodes': nodes,
        'aliases': {'foo': 14, 'bar': 14},
        'edges': edge_dicts((21, 12), (12, 13, 5), (13, 14), (15, 16), (16, 13), (18, 17), (22, 19)),
        'covers': cover_dicts((19, 22)),
        'splits': split_dicts(
            (
                14,
                [
                    (15, x_equals(15)),
                    (16, x_equals(16)),
                    (17, x_equals(17)),
                    (18, x_equals(18)),
                    (20, x_equals(20)),
                    (23, x_equals(23)),
                    (22, x_equals(22)),
                ],
            )
        ),
        'ndbranches': ndbranch_dicts((20, [(24, False), (25, True)])),
        'stuck': [23],
        'vacuous': [17],
    }
    cfg = KCFG.from_dict(d)

    expected = (
        '\n'
        '┌─ 21 (root)\n'
        '│\n'
        '│  (1 step)\n'
        '├─ 12\n'
        '│\n'
        '│  (5 steps)\n'
        '├─ 13\n'
        '│\n'
        '│  (1 step)\n'
        '├─ 14 (split, @bar, @foo)\n'
        '┃\n'
        '┃ (branch)\n'
        '┣━━┓ constraint: _==K_ ( X , 15 )\n'
        '┃  ┃ subst: V14 <- V15\n'
        '┃  │\n'
        '┃  ├─ 15\n'
        '┃  │\n'
        '┃  │  (1 step)\n'
        '┃  ├─ 16\n'
        '┃  │\n'
        '┃  │  (1 step)\n'
        '┃  └─ 13\n'
        '┃     (looped back)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 16 )\n'
        '┃  ┃ subst: V14 <- V16\n'
        '┃  │\n'
        '┃  └─ 16\n'
        '┃     (continues as previously)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 17 )\n'
        '┃  ┃ subst: V14 <- V17\n'
        '┃  │\n'
        '┃  └─ 17 (vacuous, leaf)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 18 )\n'
        '┃  ┃ subst: V14 <- V18\n'
        '┃  │\n'
        '┃  ├─ 18\n'
        '┃  │\n'
        '┃  │  (1 step)\n'
        '┃  └─ 17 (vacuous, leaf)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 20 )\n'
        '┃  ┃ subst: V14 <- V20\n'
        '┃  │\n'
        '┃  ├─ 20\n'
        '┃  ┃\n'
        '┃  ┃ (1 step)\n'
        '┃  ┣━━┓\n'
        '┃  ┃  │\n'
        '┃  ┃  └─ 24 (leaf)\n'
        '┃  ┃\n'
        '┃  ┗━━┓\n'
        '┃     │\n'
        '┃     └─ 25 (leaf)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 23 )\n'
        '┃  ┃ subst: V14 <- V23\n'
        '┃  │\n'
        '┃  └─ 23 (stuck, leaf)\n'
        '┃\n'
        '┗━━┓ constraint: _==K_ ( X , 22 )\n'
        '   ┃ subst: V14 <- V22\n'
        '   │\n'
        '   ├─ 22\n'
        '   │\n'
        '   │  (1 step)\n'
        '   ├─ 19\n'
        '   │\n'
        '   ┊  constraint: true\n'
        '   ┊  subst: V22 <- V19\n'
        '   └─ 22\n'
        '      (looped back)\n'
        '\n'
        '\n'
        '┌─ 10 (root, leaf)\n'
        '\n'
        '┌─ 11 (root, leaf)\n'
    )

    expected_full_printer = (
        '\n'
        '┌─ 21 (root)\n'
        '│     <top>\n'
        '│       V21\n'
        '│     </top>\n'
        '│\n'
        '│  (1 step)\n'
        '├─ 12\n'
        '│     <top>\n'
        '│       V12\n'
        '│     </top>\n'
        '│\n'
        '│  (5 steps)\n'
        '├─ 13\n'
        '│     <top>\n'
        '│       V13\n'
        '│     </top>\n'
        '│\n'
        '│  (1 step)\n'
        '├─ 14 (split, @bar, @foo)\n'
        '│     <top>\n'
        '│       V14\n'
        '│     </top>\n'
        '┃\n'
        '┃ (branch)\n'
        '┣━━┓ constraint: _==K_ ( X , 15 )\n'
        '┃  ┃ subst: V14 <- V15\n'
        '┃  │\n'
        '┃  ├─ 15\n'
        '┃  │     <top>\n'
        '┃  │       V15\n'
        '┃  │     </top>\n'
        '┃  │\n'
        '┃  │  (1 step)\n'
        '┃  ├─ 16\n'
        '┃  │     <top>\n'
        '┃  │       V16\n'
        '┃  │     </top>\n'
        '┃  │\n'
        '┃  │  (1 step)\n'
        '┃  └─ 13\n'
        '┃        <top>\n'
        '┃          V13\n'
        '┃        </top>\n'
        '┃     (looped back)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 16 )\n'
        '┃  ┃ subst: V14 <- V16\n'
        '┃  │\n'
        '┃  └─ 16\n'
        '┃        <top>\n'
        '┃          V16\n'
        '┃        </top>\n'
        '┃     (continues as previously)\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 17 )\n'
        '┃  ┃ subst: V14 <- V17\n'
        '┃  │\n'
        '┃  └─ 17 (vacuous, leaf)\n'
        '┃        <top>\n'
        '┃          V17\n'
        '┃        </top>\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 18 )\n'
        '┃  ┃ subst: V14 <- V18\n'
        '┃  │\n'
        '┃  ├─ 18\n'
        '┃  │     <top>\n'
        '┃  │       V18\n'
        '┃  │     </top>\n'
        '┃  │\n'
        '┃  │  (1 step)\n'
        '┃  └─ 17 (vacuous, leaf)\n'
        '┃        <top>\n'
        '┃          V17\n'
        '┃        </top>\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 20 )\n'
        '┃  ┃ subst: V14 <- V20\n'
        '┃  │\n'
        '┃  ├─ 20\n'
        '┃  │     <top>\n'
        '┃  │       V20\n'
        '┃  │     </top>\n'
        '┃  ┃\n'
        '┃  ┃ (1 step)\n'
        '┃  ┣━━┓\n'
        '┃  ┃  │\n'
        '┃  ┃  └─ 24 (leaf)\n'
        '┃  ┃        <top>\n'
        '┃  ┃          V24\n'
        '┃  ┃        </top>\n'
        '┃  ┃\n'
        '┃  ┗━━┓\n'
        '┃     │\n'
        '┃     └─ 25 (leaf)\n'
        '┃           <top>\n'
        '┃             V25\n'
        '┃           </top>\n'
        '┃           #And #Equals ( X , 25 )\n'
        '┃\n'
        '┣━━┓ constraint: _==K_ ( X , 23 )\n'
        '┃  ┃ subst: V14 <- V23\n'
        '┃  │\n'
        '┃  └─ 23 (stuck, leaf)\n'
        '┃        <top>\n'
        '┃          V23\n'
        '┃        </top>\n'
        '┃\n'
        '┗━━┓ constraint: _==K_ ( X , 22 )\n'
        '   ┃ subst: V14 <- V22\n'
        '   │\n'
        '   ├─ 22\n'
        '   │     <top>\n'
        '   │       V22\n'
        '   │     </top>\n'
        '   │\n'
        '   │  (1 step)\n'
        '   ├─ 19\n'
        '   │     <top>\n'
        '   │       V19\n'
        '   │     </top>\n'
        '   │\n'
        '   ┊  constraint: true\n'
        '   ┊  subst: V22 <- V19\n'
        '   └─ 22\n'
        '         <top>\n'
        '           V22\n'
        '         </top>\n'
        '      (looped back)\n'
        '\n'
        '\n'
        '┌─ 10 (root, leaf)\n'
        '│     <top>\n'
        '│       10\n'
        '│     </top>\n'
        '\n'
        '┌─ 11 (root, leaf)\n'
        '│     <top>\n'
        '│       V11\n'
        '│     </top>\n'
    )

    # When
    kcfg_show = KCFGShow(MockKPrint(), node_printer=NodePrinter(MockKPrint()))
    kcfg_show_full_printer = KCFGShow(MockKPrint(), node_printer=NodePrinter(MockKPrint(), full_printer=True))
    actual = '\n'.join(kcfg_show.pretty(cfg)) + '\n'
    actual_full_printer = '\n'.join(kcfg_show_full_printer.pretty(cfg)) + '\n'

    # Then
    assert actual == expected
    assert actual_full_printer == expected_full_printer


def test_no_cell_rewrite_to_dots() -> None:
    term = KApply(
        '<accounts>',
        [
            KRewrite(
                lhs=KApply(
                    '_AccountCellMap_',
                    [
                        KApply(
                            '<account>',
                            [
                                KApply(
                                    '<acctID>',
                                    [KToken('645326474426547203313410069153905908525362434349', 'Int')],
                                ),
                            ],
                        ),
                        KApply(
                            '<account>',
                            [
                                KApply(
                                    '<acctID>',
                                    [KToken('728815563385977040452943777879061427756277306518', 'Int')],
                                ),
                            ],
                        ),
                    ],
                ),
                rhs=KVariable('ACCOUNTS_FINAL', 'AccountCellMap'),
            )
        ],
    )

    result = no_cell_rewrite_to_dots(term)
    assert result == term
