from typing import Any, Dict, List, Tuple
from unittest import TestCase

from ..cterm import CTerm
from ..kast import KApply, KInner, KVariable
from ..kcfg import KCFG
from ..prelude import Bool, mlEquals, token
from ..utils import shorten_hash
from .mock_kprint import MockKPrint


def nid(i: int) -> str:
    return node(i).id


# over 10 is variables
def term(i: int) -> CTerm:
    inside: KInner = token(i)
    if i > 10:
        inside = KVariable('V' + str(i))
    return CTerm(KApply('<top>', [inside]))


def node(i: int) -> KCFG.Node:
    return KCFG.Node(term(i))


def edge(i: int, j: int) -> KCFG.Edge:
    return KCFG.Edge(node(i), node(j), Bool.true, 1)


def node_dicts(n: int) -> List[Dict[str, Any]]:
    return [node(i).to_dict() for i in range(n)]


def edge_dicts(*edges: Tuple[int, int]) -> List[Dict[str, Any]]:
    def _make_edge_dict(i, j, depth=1, condition=Bool.true):
        return {'source': nid(i), 'target': nid(j), 'condition': condition.to_dict(), 'depth': depth}

    return [_make_edge_dict(*edge) for edge in edges]


def cover_dicts(*edges: Tuple[int, int]) -> List[Dict[str, Any]]:
    return [{'source': nid(i), 'target': nid(j), 'condition': Bool.true.to_dict(), 'depth': 1} for i, j in edges]


class KCFGTestCase(TestCase):
    def test_from_dict_single_node(self):
        # Given
        d = {'nodes': node_dicts(1)}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(set(cfg.nodes), {node(0)})
        self.assertDictEqual(cfg.to_dict(), d)

    def test_from_dict_two_nodes(self):
        # Given
        d = {'nodes': node_dicts(2)}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(set(cfg.nodes), {node(0), node(1)})

    def test_from_dict_loop_edge(self):
        # Given
        d = {'nodes': node_dicts(1), 'edges': edge_dicts((0, 0))}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(set(cfg.nodes), {node(0)})
        self.assertSetEqual(set(cfg.edges()), {edge(0, 0)})
        self.assertEqual(cfg.edge(nid(0), nid(0)), edge(0, 0))
        self.assertDictEqual(cfg.to_dict(), d)

    def test_from_dict_simple_edge(self):
        # Given
        d = {'nodes': node_dicts(2), 'edges': edge_dicts((0, 1))}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(set(cfg.nodes), {node(0), node(1)})
        self.assertSetEqual(set(cfg.edges()), {edge(0, 1)})
        self.assertEqual(cfg.edge(nid(0), nid(1)), edge(0, 1))

    def test_create_node(self):
        # Given
        cfg = KCFG()

        # When
        new_node = cfg.create_node(term(0))

        # Then
        self.assertEqual(new_node, node(0))
        self.assertSetEqual(set(cfg.nodes), {node(0)})
        self.assertFalse(cfg.is_expanded(new_node.id))

    def test_remove_unknown_node(self):
        # Given
        cfg = KCFG()

        # Then
        with self.assertRaises(ValueError):
            # When
            cfg.remove_node(nid(0))

    def test_remove_node(self):
        # Given
        d = {'nodes': node_dicts(3), 'edges': edge_dicts((0, 1), (1, 2))}
        cfg = KCFG.from_dict(d)
        cfg.add_expanded(node(0).id)
        cfg.add_expanded(node(1).id)

        # When
        cfg.remove_node(nid(1))

        # Then
        self.assertSetEqual(set(cfg.nodes), {node(0), node(2)})
        self.assertSetEqual(set(cfg.edges()), set())
        self.assertFalse(cfg.is_expanded(nid(0)))
        with self.assertRaises(ValueError):
            cfg.node(nid(1))
        with self.assertRaises(ValueError):
            cfg.edge(nid(0), nid(1))
        with self.assertRaises(ValueError):
            cfg.edge(nid(1), nid(2))

    def test_cover_then_remove(self):
        # Given
        cfg = KCFG()

        # When
        node1 = cfg.create_node(CTerm(KApply('<top>', [token(1)])))
        node2 = cfg.create_node(CTerm(KApply('<top>', [KVariable('X')])))
        cover = cfg.create_cover(node1.id, node2.id)

        # Then
        self.assertTrue(cfg.is_covered(node1.id))
        self.assertFalse(cfg.is_covered(node2.id))
        self.assertFalse(cfg.is_expanded(node1.id))
        self.assertFalse(cfg.is_expanded(node2.id))
        self.assertDictEqual(dict(cover.subst), {'X': token(1)})
        self.assertEqual(cfg.covers(), [cover])

        # When
        cfg.remove_cover(node1.id, node2.id)

        # Then
        self.assertFalse(cfg.is_covered(node1.id))
        self.assertFalse(cfg.is_covered(node2.id))
        self.assertFalse(cfg.is_expanded(node1.id))
        self.assertFalse(cfg.is_expanded(node2.id))
        self.assertEqual(cfg.covers(), [])

    def test_insert_loop_edge(self):
        # Given
        d = {'nodes': node_dicts(1)}
        cfg = KCFG.from_dict(d)

        # When
        new_edge = cfg.create_edge(nid(0), nid(0), Bool.true, 1)

        # Then
        self.assertEqual(new_edge, edge(0, 0))
        self.assertSetEqual(set(cfg.nodes), {node(0)})
        self.assertSetEqual(set(cfg.edges()), {edge(0, 0)})
        self.assertEqual(cfg.edge(nid(0), nid(0)), edge(0, 0))

    def test_insert_simple_edge(self):
        # Given
        d = {'nodes': node_dicts(2)}
        cfg = KCFG.from_dict(d)

        # When
        new_edge = cfg.create_edge(nid(0), nid(1), Bool.true, 1)

        # Then
        self.assertEqual(new_edge, edge(0, 1))
        self.assertSetEqual(set(cfg.nodes), {node(0), node(1)})
        self.assertSetEqual(set(cfg.edges()), {edge(0, 1)})

    def test_get_successors(self):
        d = {'nodes': node_dicts(3), 'edges': edge_dicts((0, 1), (0, 2))}
        cfg = KCFG.from_dict(d)

        # When
        succs = set(cfg.edges(source_id=nid(0)))

        # Then
        self.assertSetEqual(succs, {edge(0, 1), edge(0, 2)})

    def test_get_predecessors(self):
        d = {'nodes': node_dicts(3), 'edges': edge_dicts((0, 2), (1, 2))}
        cfg = KCFG.from_dict(d)

        # When
        preds = set(cfg.edges(target_id=nid(2)))

        # Then
        self.assertSetEqual(preds, {edge(0, 2), edge(1, 2)})

    def test_reachable_nodes(self):
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
        self.assertSetEqual(nodes_1, {node(1), node(2), node(3), node(4)})
        self.assertSetEqual(nodes_2, {node(1), node(2), node(3), node(4), node(11)})

    def test_paths_between(self):
        # Given
        d = {
            'nodes': node_dicts(4),
            'edges': edge_dicts((0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (3, 0)),
        }
        cfg = KCFG.from_dict(d)

        # When
        paths = set(cfg.paths_between(nid(0), nid(3)))

        # Then
        self.assertSetEqual(
            paths,
            {
                (edge(0, 1), edge(1, 3)),
                (edge(0, 2), edge(2, 3)),
                (edge(0, 1), edge(1, 2), edge(2, 3)),
            },
        )

    def test_resolve(self):
        # Given
        d = {
            'nodes': node_dicts(4),
            'edges': edge_dicts((0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (3, 0)),
        }
        cfg = KCFG.from_dict(d)

        self.assertEqual(node(1), cfg.node('d33..d8'))
        self.assertEqual(node(1), cfg.node(node(1).id))

        # Matches no nodes
        with self.assertRaises(ValueError, msg='Unknown node: deadbeef..d8'):
            self.assertEqual(node(1), cfg.node('deadbeef..d8'))

        # Matches all nodes
        with self.assertRaisesRegex(ValueError, 'Multiple nodes for pattern: ...'):
            cfg.node('..')

        # Matches node(0) and node(2)
        with self.assertRaisesRegex(ValueError, 'Multiple nodes for pattern: ...'):
            cfg.node('3..')

    def test_aliases(self):
        # Given
        d = {
            'init': [nid(0)],
            'target': [nid(3)],
            'nodes': node_dicts(4),
            'edges': edge_dicts((0, 1), (1, 2)),
            'aliases': {'foo': nid(1)},
        }

        cfg = KCFG.from_dict(d)
        self.assertEqual(cfg.node('@foo'), node(1))

        self.assertEqual(cfg.node('#init'), node(0))
        self.assertEqual(cfg.node('#target'), node(3))
        cfg.add_expanded(nid(0))
        cfg.add_expanded(nid(1))
        self.assertEqual(cfg.node('#frontier'), node(2))

        cfg.add_alias('bar', node(0).id)
        cfg.add_alias('bar2', node(0).id)
        self.assertEqual(cfg.node('@bar'), node(0))
        self.assertEqual(cfg.node('@bar2'), node(0))
        cfg.remove_alias('bar')
        with self.assertRaises(ValueError, msg='Unknown alias: @bar'):
            cfg.node('@bar')

        with self.assertRaises(ValueError, msg='Duplicate alias "bar2"'):
            cfg.add_alias('bar2', node(1).id)
        with self.assertRaises(ValueError, msg='Alias may not contain "@"'):
            cfg.add_alias('@buzz', node(1).id)
        with self.assertRaises(ValueError, msg=f'Unknown node: {nid(3)}'):
            cfg.add_alias('buzz', node(9).id)

        cfg.remove_node(nid(1))
        cfg.create_node(term(1))

    def test_pretty_print(self):
        d = {
            'init': [nid(0)],
            'target': [nid(6)],
            'nodes': node_dicts(12),
            'aliases': {'foo': nid(3), 'bar': nid(3)},
            # Each of the branching edges have given depth=0
            # fmt: off
            'edges': edge_dicts((0, 1), (1, 2, 5), (2, 3),   # Initial Linear segment
                                (3, 4, 0, mlEquals(KVariable('x'), token(4))), (4, 5), (5, 2),   # Loops back
                                (3, 5, 0, mlEquals(KVariable('x'), token(5))),                   # Go to previous non-terminal node not as loop
                                (3, 6, 0, mlEquals(KVariable('x'), token(6))),                   # Terminates
                                (3, 7, 0, mlEquals(KVariable('x'), token(7))), (7, 6),           # Go to previous terminal node not as loop
                                (3, 11, 0, mlEquals(KVariable('x'), token(11))), (11, 8)         # Covered
                                ),
            # fmt: on
            'covers': cover_dicts((8, 11)),  # Loops back
            'expanded': [nid(i) for i in [0, 1, 2, 3, 4, 5, 7, 11]],
            'verified': edge_dicts((1, 2)),
        }
        cfg = KCFG.from_dict(d)

        def _short_hash(i) -> str:
            return shorten_hash(nid(i))

        self.maxDiff = None
        actual = '\n'.join(cfg.pretty(MockKPrint())) + '\n'
        self.assertMultiLineEqual(
            actual,
            f"{_short_hash(0)} (init, expanded)\n"
            f"│  (1 step)\n"
            f"├  {_short_hash(1)} (expanded)\n"
            f"│  \033[1m\33[32m(verified)\033[0m\033[0m\n"
            f"│  (5 steps)\n"
            f"├  {_short_hash(2)} (expanded)\n"
            f"│  (1 step)\n"
            f"├  {_short_hash(3)} (expanded, @bar, @foo)\n"
            f"┣━ {_short_hash(4)} (expanded)    _==K_ ( x , 4 )\n"
            f"┃   │  (1 step)\n"
            f"┃   ├  {_short_hash(5)} (expanded)\n"
            f"┃   │  (1 step)\n"
            f"┃   ├  {_short_hash(2)} (expanded)\n"
            f"┃   ┊ (looped back)\n"
            f"┃\n"
            f"┣━ {_short_hash(5)} (expanded)    _==K_ ( x , 5 )\n"
            f"┃   ┊ (continues as previously)\n"
            f"┃\n"
            f"┣━ {_short_hash(6)} (target, leaf)    _==K_ ( x , 6 )\n"
            f"┃\n"
            f"┣━ {_short_hash(7)} (expanded)    _==K_ ( x , 7 )\n"
            f"┃   │  (1 step)\n"
            f"┃   └  {_short_hash(6)} (target, leaf)\n"
            f"┃\n"
            f"┗━ {_short_hash(11)} (expanded)    _==K_ ( x , 11 )\n"
            f"    │  (1 step)\n"
            f"    ├  {_short_hash(8)} (leaf)\n"
            f"    ┊  constraint: true\n"
            f"    ┊  subst:\n"
            f"    ┊    V11 |-> 8\n"
            f"    └╌ {_short_hash(11)} (expanded)\n"
            f"        ┊ (looped back)\n"
            f"\n"
            f"\033[1m{_short_hash(10)} (frontier, leaf)\033[0m\n"
            f"\033[1m{_short_hash(9)} (frontier, leaf)\033[0m\n",
        )
