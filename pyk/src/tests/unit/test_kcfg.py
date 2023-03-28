from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KVariable
from pyk.kcfg import KCFG
from pyk.prelude.ml import mlEquals, mlTop
from pyk.prelude.utils import token
from pyk.utils import shorten_hash

from .mock_kprint import MockKPrint

if TYPE_CHECKING:
    from typing import Any, Dict, Iterable, List, Optional, Tuple

    from pyk.kast import KInner


def nid(i: int) -> str:
    return node(i).id


# over 10 is variables
def term(i: int) -> CTerm:
    inside: KInner = token(i)
    if i > 10:
        inside = KVariable('V' + str(i))
    return CTerm(KApply('<top>', [inside]))


def node_short_info(ct: CTerm) -> Iterable[str]:
    return MockKPrint().pretty_print(ct.kast).split('\n')


def node(i: int) -> KCFG.Node:
    return KCFG.Node(term(i))


def edge(i: int, j: int) -> KCFG.Edge:
    return KCFG.Edge(node(i), node(j), mlTop(), 0)


def node_dicts(n: int) -> List[Dict[str, Any]]:
    return [node(i).to_dict() for i in range(n)]


def edge_dicts(*edges: Iterable) -> List[Dict[str, Any]]:
    def _make_edge_dict(i: int, j: int, depth: int = 0, condition: Optional[KInner] = None) -> Dict[str, Any]:
        if condition is None:
            condition = mlTop()
        return {'source': nid(i), 'target': nid(j), 'condition': condition.to_dict(), 'depth': depth}

    return [_make_edge_dict(*edge) for edge in edges]


def cover_dicts(*edges: Tuple[int, int]) -> List[Dict[str, Any]]:
    covers = []
    for i, j in edges:
        csubst = term(j).match_with_constraint(term(i))
        assert csubst is not None
        covers.append({'source': nid(i), 'target': nid(j), 'csubst': csubst.to_dict()})
    return covers


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
    node1 = cfg.create_node(CTerm(KApply('<top>', [token(1)])))
    node2 = cfg.create_node(CTerm(KApply('<top>', [KVariable('X')])))
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
    new_edge = cfg.create_edge(nid(0), nid(0), mlTop(), 0)

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
    new_edge = cfg.create_edge(nid(0), nid(1), mlTop(), 0)

    # Then
    assert new_edge == edge(0, 1)
    assert set(cfg.nodes) == {node(0), node(1)}
    assert set(cfg.edges()) == {edge(0, 1)}


def test_get_successors() -> None:
    d = {'nodes': node_dicts(3), 'edges': edge_dicts((0, 1), (0, 2))}
    cfg = KCFG.from_dict(d)

    # When
    succs = set(cfg.edges(source_id=nid(0)))

    # Then
    assert succs == {edge(0, 1), edge(0, 2)}


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
        'nodes': node_dicts(12),
        'edges': edge_dicts((0, 1), (0, 5), (0, 11), (1, 2), (1, 3), (2, 4), (3, 4), (4, 1)),
        'covers': cover_dicts((4, 11)),
    }
    cfg = KCFG.from_dict(d)

    # When
    nodes_1 = cfg.reachable_nodes(nid(1))
    nodes_2 = cfg.reachable_nodes(nid(1), traverse_covers=True)

    # Then
    assert nodes_1 == {node(1), node(2), node(3), node(4)}
    assert nodes_2 == {node(1), node(2), node(3), node(4), node(11)}


def test_paths_between() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
        'edges': edge_dicts((0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (3, 0)),
    }
    cfg = KCFG.from_dict(d)

    # When
    paths = set(cfg.paths_between(nid(0), nid(3)))

    # Then
    assert paths == {
        (edge(0, 1), edge(1, 3)),
        (edge(0, 2), edge(2, 3)),
        (edge(0, 1), edge(1, 2), edge(2, 3)),
    }


def test_resolve() -> None:
    # Given
    d = {
        'nodes': node_dicts(4),
        'edges': edge_dicts((0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (3, 0)),
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
    d = {
        'init': [nid(0)],
        'target': [nid(6)],
        'nodes': node_dicts(13),
        'aliases': {'foo': nid(3), 'bar': nid(3)},
        # Each of the branching edges have given depth=0
        # fmt: off
        'edges': edge_dicts((0, 1, 1), (1, 2, 5), (2, 3, 1),                                        # Initial Linear segment
                            (3, 4, 0, mlEquals(KVariable('x'), token(4))), (4, 5, 1), (5, 2, 1),    # Loops back
                            (3, 5, 0, mlEquals(KVariable('x'), token(5))),                          # Go to previous non-terminal node not as loop
                            (3, 6, 0, mlEquals(KVariable('x'), token(6))),                          # Terminates
                            (3, 7, 0, mlEquals(KVariable('x'), token(7))), (7, 6, 1),               # Go to previous terminal node not as loop
                            (3, 9, 0, mlEquals(KVariable('x'), token(9))),                          # Frontier
                            (3, 10, 0, mlEquals(KVariable('x'), token(10))),                        # Stuck
                            (3, 11, 0, mlEquals(KVariable('x'), token(11))), (11, 8, 1),            # Covered
                            ),
        # fmt: on
        'covers': cover_dicts((8, 11)),  # Loops back
        'expanded': [nid(i) for i in [0, 1, 2, 3, 4, 5, 7, 10, 11]],
    }
    cfg = KCFG.from_dict(d)

    def _short_hash(i: int) -> str:
        return shorten_hash(nid(i))

    expected = (
        f'\n'
        f'┌─ {_short_hash(0)} (init, expanded)\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(1)} (expanded)\n'
        f'│\n'
        f'│  (5 steps)\n'
        f'├─ {_short_hash(2)} (expanded)\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(3)} (expanded, @bar, @foo)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 4 )\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(4)} (expanded)\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  ├─ {_short_hash(5)} (expanded)\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(2)} (expanded)\n'
        f'┃     (looped back)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 5 )\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(5)} (expanded)\n'
        f'┃     (continues as previously)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 6 )\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(6)} (target, leaf)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 7 )\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(7)} (expanded)\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(6)} (target, leaf)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 9 )\n'
        f'┃  │\n'
        f'┃  └─ \033[1m{_short_hash(9)} (frontier, leaf)\033[0m\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 10 )\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(10)} (expanded, stuck, leaf)\n'
        f'┃     (stuck)\n'
        f'┃\n'
        f'┗━━┓ constraint: #Equals ( x , 11 )\n'
        f'   │\n'
        f'   ├─ {_short_hash(11)} (expanded)\n'
        f'   │\n'
        f'   │  (1 step)\n'
        f'   ├─ {_short_hash(8)} (leaf)\n'
        f'   │\n'
        f'   ┊  constraint: true\n'
        f'   ┊  subst: V11 <- 8\n'
        f'   └─ {_short_hash(11)} (expanded)\n'
        f'      (looped back)\n'
        f'\n'
        f'\n'
        f'Target Nodes:\n'
        f'\n'
        f'{_short_hash(6)} (target, leaf)\n'
        f'\n'
        f'Remaining Nodes:\n'
        f'\n'
        f'\033[1m{_short_hash(12)} (frontier, leaf)\033[0m\n'
    )

    expected_short_info = (
        f'\n'
        f'┌─ {_short_hash(0)} (init, expanded)\n'
        f'│    <top>\n'
        f'│      0\n'
        f'│    </top>\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(1)} (expanded)\n'
        f'│    <top>\n'
        f'│      1\n'
        f'│    </top>\n'
        f'│\n'
        f'│  (5 steps)\n'
        f'├─ {_short_hash(2)} (expanded)\n'
        f'│    <top>\n'
        f'│      2\n'
        f'│    </top>\n'
        f'│\n'
        f'│  (1 step)\n'
        f'├─ {_short_hash(3)} (expanded, @bar, @foo)\n'
        f'│    <top>\n'
        f'│      3\n'
        f'│    </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 4 )\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(4)} (expanded)\n'
        f'┃  │    <top>\n'
        f'┃  │      4\n'
        f'┃  │    </top>\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  ├─ {_short_hash(5)} (expanded)\n'
        f'┃  │    <top>\n'
        f'┃  │      5\n'
        f'┃  │    </top>\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(2)} (expanded)\n'
        f'┃       <top>\n'
        f'┃         2\n'
        f'┃       </top>\n'
        f'┃     (looped back)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 5 )\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(5)} (expanded)\n'
        f'┃       <top>\n'
        f'┃         5\n'
        f'┃       </top>\n'
        f'┃     (continues as previously)\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 6 )\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(6)} (target, leaf)\n'
        f'┃       <top>\n'
        f'┃         6\n'
        f'┃       </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 7 )\n'
        f'┃  │\n'
        f'┃  ├─ {_short_hash(7)} (expanded)\n'
        f'┃  │    <top>\n'
        f'┃  │      7\n'
        f'┃  │    </top>\n'
        f'┃  │\n'
        f'┃  │  (1 step)\n'
        f'┃  └─ {_short_hash(6)} (target, leaf)\n'
        f'┃       <top>\n'
        f'┃         6\n'
        f'┃       </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 9 )\n'
        f'┃  │\n'
        f'┃  └─ \033[1m{_short_hash(9)} (frontier, leaf)\033[0m\n'
        f'┃       <top>\n'
        f'┃         9\n'
        f'┃       </top>\n'
        f'┃\n'
        f'┣━━┓ constraint: #Equals ( x , 10 )\n'
        f'┃  │\n'
        f'┃  └─ {_short_hash(10)} (expanded, stuck, leaf)\n'
        f'┃       <top>\n'
        f'┃         10\n'
        f'┃       </top>\n'
        f'┃     (stuck)\n'
        f'┃\n'
        f'┗━━┓ constraint: #Equals ( x , 11 )\n'
        f'   │\n'
        f'   ├─ {_short_hash(11)} (expanded)\n'
        f'   │    <top>\n'
        f'   │      V11\n'
        f'   │    </top>\n'
        f'   │\n'
        f'   │  (1 step)\n'
        f'   ├─ {_short_hash(8)} (leaf)\n'
        f'   │    <top>\n'
        f'   │      8\n'
        f'   │    </top>\n'
        f'   │\n'
        f'   ┊  constraint: true\n'
        f'   ┊  subst: V11 <- 8\n'
        f'   └─ {_short_hash(11)} (expanded)\n'
        f'        <top>\n'
        f'          V11\n'
        f'        </top>\n'
        f'      (looped back)\n'
        f'\n'
        f'\n'
        f'Target Nodes:\n'
        f'\n'
        f'{_short_hash(6)} (target, leaf)\n'
        f' <top>\n'
        f'   6\n'
        f' </top>\n'
        f'\n'
        f'Remaining Nodes:\n'
        f'\n'
        f'\033[1m{_short_hash(12)} (frontier, leaf)\033[0m\n'
        f' <top>\n'
        f'   V12\n'
        f' </top>\n'
    )

    # When
    actual = '\n'.join(cfg.pretty(MockKPrint())) + '\n'
    actual_short_info = '\n'.join(cfg.pretty(MockKPrint(), node_printer=node_short_info)) + '\n'

    # Then
    assert actual == expected
    assert actual_short_info == expected_short_info
