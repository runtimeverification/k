from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KVariable
from pyk.kcfg import KCFG, KCFGShow
from pyk.prelude.ml import mlEquals, mlTop
from pyk.prelude.utils import token
from pyk.utils import shorten_hash

from .mock_kprint import MockKPrint

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Any

    from pyk.kast import KInner


def nid(i: int) -> str:
    return node(i).id


# over 10 is variables
def term(i: int) -> CTerm:
    inside: KInner = token(i)
    if i > 10:
        inside = KVariable('V' + str(i))
    return CTerm(KApply('<top>', [inside]), ())


def node_short_info(ct: CTerm) -> Iterable[str]:
    return MockKPrint().pretty_print(ct.kast).split('\n')


def node(i: int) -> KCFG.Node:
    return KCFG.Node(term(i))


def edge(i: int, j: int) -> KCFG.Edge:
    return KCFG.Edge(node(i), node(j), 1)


def cover(i: int, j: int) -> KCFG.Cover:
    csubst = term(j).match_with_constraint(term(i))
    assert csubst is not None
    return KCFG.Cover(node(i), node(j), csubst)


def split(i: int, js: Iterable[int]) -> KCFG.Split:
    split_substs = []
    for j in js:
        csubst = term(i).match_with_constraint(term(j))
        assert csubst is not None
        split_substs.append(csubst)
    return KCFG.Split(node(i), zip((node(j) for j in js), split_substs, strict=True))


def node_dicts(n: int, start: int = 0) -> list[dict[str, Any]]:
    return [node(i).to_dict() for i in range(start, n)]


def edge_dicts(*edges: Iterable) -> list[dict[str, Any]]:
    def _make_edge_dict(i: int, j: int, depth: int = 1) -> dict[str, Any]:
        return {'source': nid(i), 'target': nid(j), 'depth': depth}

    return [_make_edge_dict(*edge) for edge in edges]


def cover_dicts(*edges: tuple[int, int]) -> list[dict[str, Any]]:
    covers = []
    for i, j in edges:
        csubst = term(j).match_with_constraint(term(i))
        assert csubst is not None
        covers.append({'source': nid(i), 'target': nid(j), 'csubst': csubst.to_dict()})
    return covers


def split_dicts(*edges: tuple[int, Iterable[tuple[int, KInner]]]) -> dict[str, Any]:
    splits = {}
    for s, ts in edges:
        targets = {}
        for t, constraint in ts:
            csubst = term(s).match_with_constraint(term(t))
            assert csubst is not None
            csubst = csubst.add_constraint(constraint)
            targets[nid(t)] = csubst.to_dict()
        splits[nid(t)] = {'source': nid(s), 'targets': targets}
    return splits


def test_from_dict_single_node() -> None:
    # Given
    d = {'nodes': node_dicts(1)}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(0)}
    assert cfg.to_dict() == d


def test_from_dict_two_nodes() -> None:
    # Given
    d = {'nodes': node_dicts(2)}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(0), node(1)}


def test_from_dict_loop_edge() -> None:
    # Given
    d = {'nodes': node_dicts(1), 'edges': edge_dicts((0, 0))}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(0)}
    assert set(cfg.edges()) == {edge(0, 0)}
    assert cfg.edge(nid(0), nid(0)) == edge(0, 0)
    assert cfg.to_dict() == d


def test_from_dict_simple_edge() -> None:
    # Given
    d = {'nodes': node_dicts(2), 'edges': edge_dicts((0, 1))}

    # When
    cfg = KCFG.from_dict(d)

    # Then
    assert set(cfg.nodes) == {node(0), node(1)}
    assert set(cfg.edges()) == {edge(0, 1)}
    assert cfg.edge(nid(0), nid(1)) == edge(0, 1)


def test_create_node() -> None:
    # Given
    cfg = KCFG()

    # When
    new_node = cfg.create_node(term(0))

    # Then
    assert new_node == node(0)
    assert set(cfg.nodes) == {node(0)}
    assert not cfg.is_expanded(new_node.id)


def test_remove_unknown_node() -> None:
    # Given
    cfg = KCFG()

    # Then
    with pytest.raises(ValueError):
        # When
        cfg.remove_node(nid(0))


def test_remove_node() -> None:
    # Given
    d = {'nodes': node_dicts(3), 'edges': edge_dicts((0, 1), (1, 2))}
    cfg = KCFG.from_dict(d)
    cfg.add_expanded(node(0).id)
    cfg.add_expanded(node(1).id)

    # When
    cfg.remove_node(nid(1))

    # Then
    assert set(cfg.nodes) == {node(0), node(2)}
    assert set(cfg.edges()) == set()
    assert not cfg.is_expanded(nid(0))
    with pytest.raises(ValueError):
        cfg.node(nid(1))
    with pytest.raises(ValueError):
        cfg.edge(nid(0), nid(1))
    with pytest.raises(ValueError):
        cfg.edge(nid(1), nid(2))


def test_cover_then_remove() -> None:
    # Given
    cfg = KCFG()

    # When
    node1 = cfg.create_node(CTerm(KApply('<top>', token(1)), ()))
    node2 = cfg.create_node(CTerm(KApply('<top>', KVariable('X')), ()))
    cover = cfg.create_cover(node1.id, node2.id)

    # Then
    assert cfg.is_covered(node1.id)
    assert not cfg.is_covered(node2.id)
    assert not cfg.is_expanded(node1.id)
    assert not cfg.is_expanded(node2.id)
    assert dict(cover.csubst.subst) == {'X': token(1)}
    assert cfg.covers() == [cover]

    # When
    cfg.remove_cover(node1.id, node2.id)

    # Then
    assert not cfg.is_covered(node1.id)
    assert not cfg.is_covered(node2.id)
    assert not cfg.is_expanded(node1.id)
    assert not cfg.is_expanded(node2.id)
    assert cfg.covers() == []


def test_insert_loop_edge() -> None:
    # Given
    d = {'nodes': node_dicts(1)}
    cfg = KCFG.from_dict(d)

    # When
    new_edge = cfg.create_edge(nid(0), nid(0), 1)

    # Then
    assert new_edge == edge(0, 0)
    assert set(cfg.nodes) == {node(0)}
    assert set(cfg.edges()) == {edge(0, 0)}
    assert cfg.edge(nid(0), nid(0)) == edge(0, 0)


def test_insert_simple_edge() -> None:
    # Given
    d = {'nodes': node_dicts(2)}
    cfg = KCFG.from_dict(d)

    # When
    new_edge = cfg.create_edge(nid(0), nid(1), 1)

    # Then
    assert new_edge == edge(0, 1)
    assert set(cfg.nodes) == {node(0), node(1)}
    assert set(cfg.edges()) == {edge(0, 1)}


def test_get_successors() -> None:
    d = {
        'nodes': node_dicts(15),
        'edges': edge_dicts((11, 12)),
        'splits': split_dicts((12, [(13, mlTop()), (14, mlTop())])),
        'covers': cover_dicts((14, 11)),
    }
    cfg = KCFG.from_dict(d)

    # When
    edges = set(cfg.edges(source_id=nid(11)))
    covers = set(cfg.covers(source_id=nid(14)))
    splits = set(cfg.splits(source_id=nid(12)))

    # Then
    assert edges == {edge(11, 12)}
    assert covers == {cover(14, 11)}
    assert splits == {split(12, [13, 14])}


def test_get_predecessors() -> None:
    d = {'nodes': node_dicts(3), 'edges': edge_dicts((0, 2), (1, 2))}
    cfg = KCFG.from_dict(d)

    # When
    preds = set(cfg.edges(target_id=nid(2)))

    # Then
    assert preds == {edge(0, 2), edge(1, 2)}


def test_reachable_nodes() -> None:
    # Given
    d = {
        'nodes': node_dicts(18),
        'edges': edge_dicts((12, 14), (13, 14), (14, 11)),
        'covers': cover_dicts((11, 12)),
        'splits': split_dicts(
            (15, [(11, mlTop()), (12, mlTop()), (16, mlTop())]), (16, [(11, mlTop()), (17, mlTop())])
        ),
    }
    cfg = KCFG.from_dict(d)

    # When
    nodes_1 = cfg.reachable_nodes(nid(11))
    nodes_2 = cfg.reachable_nodes(nid(11), traverse_covers=True)
    nodes_3 = cfg.reachable_nodes(nid(15), traverse_covers=True)
    nodes_4 = cfg.reachable_nodes(nid(12), traverse_covers=True, reverse=True)

    # Then
    assert nodes_1 == {node(11)}
    assert nodes_2 == {node(11), node(12), node(14)}
    assert nodes_3 == {node(15), node(11), node(12), node(16), node(17), node(14)}
    assert nodes_4 == {node(12), node(15), node(11), node(14), node(16), node(13)}


def test_paths_between() -> None:
    # Given
    d = {
        'nodes': node_dicts(18),
        'edges': edge_dicts((12, 14), (13, 14), (14, 11)),
        'covers': cover_dicts((11, 12)),
        'splits': split_dicts(
            (15, [(11, mlTop()), (12, mlTop()), (16, mlTop())]), (16, [(11, mlTop()), (17, mlTop())])
        ),
    }
    cfg = KCFG.from_dict(d)

    # When
    paths = set(cfg.paths_between(nid(15), nid(14)))

    # Then
    assert paths == {
        (split(15, [11]), cover(11, 12), edge(12, 14)),
        (split(15, [12]), edge(12, 14)),
        (split(15, [16]), split(16, [11]), cover(11, 12), edge(12, 14)),
    }


def test_resolve() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
    }
    cfg = KCFG.from_dict(d)

    assert node(1) == cfg.node('d33..d8')
    assert node(1) == cfg.node(node(1).id)

    # Matches no nodes
    with pytest.raises(ValueError, match='Unknown node: deadbeef..d8'):
        cfg.node('deadbeef..d8')

    # Matches all nodes
    with pytest.raises(ValueError, match='Multiple nodes for pattern: ...'):
        cfg.node('..')

    # Matches node(0) and node(2)
    with pytest.raises(ValueError, match='Multiple nodes for pattern: ...'):
        cfg.node('3..')


def test_aliases() -> None:
    # Given
    d = {
        'init': [nid(0)],
        'target': [nid(3)],
        'nodes': node_dicts(4),
        'edges': edge_dicts((0, 1), (1, 2)),
        'aliases': {'foo': nid(1)},
    }

    cfg = KCFG.from_dict(d)
    assert cfg.node('@foo'), node(1)

    assert cfg.node('#init'), node(0)
    assert cfg.node('#target'), node(3)
    cfg.add_expanded(nid(0))
    cfg.add_expanded(nid(1))
    assert cfg.node('#frontier'), node(2)

    cfg.add_alias('bar', node(0).id)
    cfg.add_alias('bar2', node(0).id)
    assert cfg.node('@bar'), node(0)
    assert cfg.node('@bar2'), node(0)
    cfg.remove_alias('bar')
    with pytest.raises(ValueError, match='Unknown alias: @bar'):
        cfg.node('@bar')

    with pytest.raises(ValueError, match='Duplicate alias: bar2'):
        cfg.add_alias('bar2', node(1).id)
    with pytest.raises(ValueError, match='Alias may not contain "@"'):
        cfg.add_alias('@buzz', node(1).id)
    with pytest.raises(ValueError, match=f'Unknown node: {nid(9)}'):
        cfg.add_alias('buzz', node(9).id)

    cfg.remove_node(nid(1))
    cfg.create_node(term(1))


def test_pretty_print() -> None:
    def _x_equals(i: int) -> KInner:
        return mlEquals(KVariable('x'), token(i))

    d = {
        'init': [nid(20)],
        'target': [nid(16)],
        'nodes': node_dicts(24, start=9),
        'aliases': {'foo': nid(13), 'bar': nid(13)},
        'edges': edge_dicts((20, 11), (11, 12, 5), (12, 13), (14, 15), (15, 12), (17, 16), (21, 18)),
        'covers': cover_dicts((18, 21)),
        'splits': split_dicts(
            (
                13,
                [
                    (14, _x_equals(14)),
                    (15, _x_equals(15)),
                    (16, _x_equals(16)),
                    (17, _x_equals(17)),
                    (19, _x_equals(19)),
                    (22, _x_equals(22)),
                    (21, _x_equals(21)),
                ],
            )
        ),
        'expanded': [nid(i) for i in [20, 11, 12, 13, 14, 15, 17, 21, 22]],
    }
    cfg = KCFG.from_dict(d)

    def _short_hash(i: int) -> str:
        return shorten_hash(nid(i))

    expected = (
        f'\n'
        f'┌─ {_short_hash(20)} (init, expanded)\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(11)} (expanded)\n'
        f'│\n'
        f'│  (5 steps)\n'
        f'├─ {_short_hash(12)} (expanded)\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(13)} (expanded, split, @bar, @foo)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 14 )\n'
        f'┃  ┃ subst: V13 <- V14\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(14)} (expanded)\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  ├─ {_short_hash(15)} (expanded)\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(12)} (expanded)\n'
        f'┃     (looped back)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 15 )\n'
        f'┃  ┃ subst: V13 <- V15\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(15)} (expanded)\n'
        f'┃     (continues as previously)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 16 )\n'
        f'┃  ┃ subst: V13 <- V16\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(16)} (target, leaf)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 17 )\n'
        f'┃  ┃ subst: V13 <- V17\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(17)} (expanded)\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(16)} (target, leaf)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 19 )\n'
        f'┃  ┃ subst: V13 <- V19\n'
        f'┃  │\n'
        f'┃  └─ \033[1m{_short_hash(19)} (frontier, leaf)\033[0m\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 22 )\n'
        f'┃  ┃ subst: V13 <- V22\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(22)} (expanded, stuck, leaf)\n'
        f'┃     (stuck)\n'
        f'┃\n'
        f'┗━━┓ constraint: #Equals ( x , 21 )\n'
        f'   ┃ subst: V13 <- V21\n'
        f'   │\n'
        f'   ├─ {_short_hash(21)} (expanded)\n'
        f'   │\n'
        f'   │  (1 step)\n'
        f'   ├─ {_short_hash(18)} (leaf)\n'
        f'   │\n'
        f'   ┊  constraint: true\n'
        f'   ┊  subst: V21 <- V18\n'
        f'   └─ {_short_hash(21)} (expanded)\n'
        f'      (looped back)\n'
        f'\n'
        f'\n'
        f'Target Nodes:\n'
        f'\n'
        f'{_short_hash(16)} (target, leaf)\n'
        f'\n'
        f'Remaining Nodes:\n'
        f'\n'
        f'\033[1m{_short_hash(10)} (frontier, leaf)\033[0m\n'
        f'\n'
        f'\033[1m{_short_hash(9)} (frontier, leaf)\033[0m\n'
        f'\n'
        f'\033[1m{_short_hash(23)} (frontier, leaf)\033[0m\n'
    )

    expected_short_info = (
        f'\n'
        f'┌─ {_short_hash(20)} (init, expanded)\n'
        f'│    <top>\n'
        f'│      V20\n'
        f'│    </top>\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(11)} (expanded)\n'
        f'│    <top>\n'
        f'│      V11\n'
        f'│    </top>\n'
        f'│\n'
        f'│  (5 steps)\n'
        f'├─ {_short_hash(12)} (expanded)\n'
        f'│    <top>\n'
        f'│      V12\n'
        f'│    </top>\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(13)} (expanded, split, @bar, @foo)\n'
        f'│    <top>\n'
        f'│      V13\n'
        f'│    </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 14 )\n'
        f'┃  ┃ subst: V13 <- V14\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(14)} (expanded)\n'
        f'┃  │    <top>\n'
        f'┃  │      V14\n'
        f'┃  │    </top>\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  ├─ {_short_hash(15)} (expanded)\n'
        f'┃  │    <top>\n'
        f'┃  │      V15\n'
        f'┃  │    </top>\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(12)} (expanded)\n'
        f'┃       <top>\n'
        f'┃         V12\n'
        f'┃       </top>\n'
        f'┃     (looped back)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 15 )\n'
        f'┃  ┃ subst: V13 <- V15\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(15)} (expanded)\n'
        f'┃       <top>\n'
        f'┃         V15\n'
        f'┃       </top>\n'
        f'┃     (continues as previously)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 16 )\n'
        f'┃  ┃ subst: V13 <- V16\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(16)} (target, leaf)\n'
        f'┃       <top>\n'
        f'┃         V16\n'
        f'┃       </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 17 )\n'
        f'┃  ┃ subst: V13 <- V17\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(17)} (expanded)\n'
        f'┃  │    <top>\n'
        f'┃  │      V17\n'
        f'┃  │    </top>\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(16)} (target, leaf)\n'
        f'┃       <top>\n'
        f'┃         V16\n'
        f'┃       </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 19 )\n'
        f'┃  ┃ subst: V13 <- V19\n'
        f'┃  │\n'
        f'┃  └─ \033[1m{_short_hash(19)} (frontier, leaf)\033[0m\n'
        f'┃       <top>\n'
        f'┃         V19\n'
        f'┃       </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 22 )\n'
        f'┃  ┃ subst: V13 <- V22\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(22)} (expanded, stuck, leaf)\n'
        f'┃       <top>\n'
        f'┃         V22\n'
        f'┃       </top>\n'
        f'┃     (stuck)\n'
        f'┃\n'
        f'┗━━┓ constraint: #Equals ( x , 21 )\n'
        f'   ┃ subst: V13 <- V21\n'
        f'   │\n'
        f'   ├─ {_short_hash(21)} (expanded)\n'
        f'   │    <top>\n'
        f'   │      V21\n'
        f'   │    </top>\n'
        f'   │\n'
        f'   │  (1 step)\n'
        f'   ├─ {_short_hash(18)} (leaf)\n'
        f'   │    <top>\n'
        f'   │      V18\n'
        f'   │    </top>\n'
        f'   │\n'
        f'   ┊  constraint: true\n'
        f'   ┊  subst: V21 <- V18\n'
        f'   └─ {_short_hash(21)} (expanded)\n'
        f'        <top>\n'
        f'          V21\n'
        f'        </top>\n'
        f'      (looped back)\n'
        f'\n'
        f'\n'
        f'Target Nodes:\n'
        f'\n'
        f'{_short_hash(16)} (target, leaf)\n'
        f' <top>\n'
        f'   V16\n'
        f' </top>\n'
        f'\n'
        f'Remaining Nodes:\n'
        f'\n'
        f'\033[1m{_short_hash(10)} (frontier, leaf)\033[0m\n'
        f' <top>\n'
        f'   10\n'
        f' </top>\n'
        f'\n'
        f'\033[1m{_short_hash(9)} (frontier, leaf)\033[0m\n'
        f' <top>\n'
        f'   9\n'
        f' </top>\n'
        f'\n'
        f'\033[1m{_short_hash(23)} (frontier, leaf)\033[0m\n'
        f' <top>\n'
        f'   V23\n'
        f' </top>\n'
    )

    # When
    kcfg_show = KCFGShow(MockKPrint())
    actual = '\n'.join(kcfg_show.pretty(cfg)) + '\n'
    actual_short_info = '\n'.join(kcfg_show.pretty(cfg, node_printer=node_short_info)) + '\n'

    # Then
    assert actual == expected
    assert actual_short_info == expected_short_info
