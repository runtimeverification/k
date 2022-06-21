from typing import Any, Dict, List, Tuple, cast
from unittest import TestCase

from ..cterm import CTerm
from ..kast import TRUE, KApply, KAst, KInner, KVariable
from ..kcfg import KCFG
from ..ktool import KPrint
from ..prelude import token


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
    return KCFG.Edge(node(i), node(j), TRUE, 1)


def node_dicts(n: int) -> List[Dict[str, Any]]:
    return [node(i).to_dict() for i in range(n)]


def edge_dicts(*edges: Tuple[int, int]) -> List[Dict[str, Any]]:

    def _make_edge_dict(i, j, depth=1):
        return {'source': nid(i), 'target': nid(j), 'condition': TRUE.to_dict(), 'depth': depth}

    return [_make_edge_dict(*edge) for edge in edges]


def cover_dicts(*edges: Tuple[int, int]) -> List[Dict[str, Any]]:
    return [
        {'source': nid(i), 'target': nid(j), 'condition': TRUE.to_dict(), 'depth': 1}
        for i, j in edges
    ]


class MockKPrint:
    def pretty_print(self, term: KAst) -> str:
        return str(term)


def mock_kprint() -> KPrint:
    return cast(KPrint, MockKPrint())


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
        new_edge = cfg.create_edge(nid(0), nid(0), TRUE, 1)

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
        new_edge = cfg.create_edge(nid(0), nid(1), TRUE, 1)

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
            'nodes': node_dicts(2),
            'edges': edge_dicts((0, 1)),
            'aliases': {'foo': nid(1)}
        }

        cfg = KCFG.from_dict(d)
        self.assertEqual(cfg.node('foo'), node(1))
        self.assertEqual(cfg.short_id(node(1)), 'foo')

        self.assertNotEqual(cfg.short_id(node(0)), 'bar')
        cfg.add_alias('bar', node(0).id)
        self.assertEqual(cfg.node('bar'), node(0))
        cfg.remove_alias('bar')
        with self.assertRaisesRegex(ValueError, 'Bad short hash: bar'):
            cfg.node('bar')
        self.assertNotEqual(cfg.short_id(node(0)), 'bar')

        with self.assertRaisesRegex(ValueError, 'Unknown node: '):
            cfg.add_alias('buzz', node(3).id)

        cfg.remove_node(nid(1))
        cfg.create_node(term(1))
        self.assertNotEqual(cfg.short_id(node(1)), 'foo')

    def test_pretty_print(self):
        d = {
            'init': [nid(0)],
            'target': [nid(6)],
            'nodes': node_dicts(12),
            'aliases': {'foo': nid(3)},
                                                             # Each of the branching edges have given depth=0 # noqa: E131
            'edges': edge_dicts((0, 1), (1, 2, 5), (2, 3),   # Initial Linear segment
                                (3, 4, 0), (4, 5), (5, 2),   # Loops back
                                (3, 5, 0),                   # Go to previous non-terminal node not as loop
                                (3, 6, 0),                   # Terminates
                                (3, 7, 0), (7, 6),           # Go to previous terminal node not as loop
                                (3, 11, 0), (11, 8)          # Covered
                                ),
            'covers': cover_dicts((8, 11)),                  # Loops back
            'expanded': [nid(i) for i in [0, 1, 2, 3, 4, 5, 7, 11]],
        }
        cfg = KCFG.from_dict(d)

        def _short_id(i) -> str:
            return cfg.short_id(node(i))

        self.maxDiff = None
        actual = '\n'.join(cfg.pretty_print(mock_kprint())) + '\n'
        self.assertMultiLineEqual(actual,
                                  f"{_short_id(0)} (init, expanded)\n"
                                  f"│  (1 step)\n"
                                  f"├  {_short_id(1)} (expanded)\n"
                                  f"│  (5 steps)\n"
                                  f"├  {_short_id(2)} (expanded)\n"
                                  f"│  (1 step)\n"
                                  f"├  {_short_id(3)} (expanded)\n"
                                  f"┢━ {_short_id(4)} (expanded)\n"
                                  f"┃   │  (1 step)\n"
                                  f"┃   ├  {_short_id(5)} (expanded)\n"
                                  f"┃   │  (1 step)\n"
                                  f"┃   ├  {_short_id(2)} (expanded)\n"
                                  f"┃   ┊ (looped back)\n"
                                  f"┃\n"
                                  f"┣━ {_short_id(5)} (expanded)\n"
                                  f"┃   ┊ (continues as previously)\n"
                                  f"┃\n"
                                  f"┣━ {_short_id(6)} (target, leaf)\n"
                                  f"┃\n"
                                  f"┣━ {_short_id(7)} (expanded)\n"
                                  f"┃   │  (1 step)\n"
                                  f"┃   └  {_short_id(6)} (target, leaf)\n"
                                  f"┃\n"
                                  f"┗━ {_short_id(11)} (expanded)\n"
                                  f"    │  (1 step)\n"
                                  f"    ├  {_short_id(8)} (leaf)\n"
                                  f"    │  constraint: KApply(label=KLabel(name='#Top', params=(KSort(name='GeneratedTopCell'),)), args=())\n"
                                  f"    │  subst:\n"
                                  f"    │    KApply(label=KLabel(name='#Equals', params=(KSort(name='K'), KSort(name='K'))), args=(KVariable(name='V11'), KToken(token='8', sort=KSort(name='Int'))))\n"
                                  f"    ├  {_short_id(11)} (expanded)\n"
                                  f"    ┊ (looped back)\n\n"
                                  f""
                                  f"{_short_id(9)} (frontier, leaf)\n"
                                  f"{_short_id(10)} (frontier, leaf)\n"
                                  )
