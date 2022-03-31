from typing import Any, Dict, List, Tuple
from unittest import TestCase

from ..cterm import CTerm
from ..kast import TRUE, KApply
from ..kcfg import KCFG
from ..prelude import token


def nid(i: int) -> str:
    return node(i).id


def term(i: int) -> CTerm:
    return CTerm(KApply('<top>', [token(i)]))


def node(i: int) -> KCFG.Node:
    return KCFG.Node(term(i))


def edge(i: int, j: int) -> KCFG.Edge:
    return KCFG.Edge(node(i), node(j), TRUE, 1)


def node_dicts(n: int) -> List[Dict[str, Any]]:
    return [node(i).to_dict() for i in range(n)]


def edge_dicts(*edges: Tuple[int, int]) -> List[Dict[str, Any]]:
    return [
        {'source': nid(i), 'target': nid(j), 'condition': TRUE.to_dict(), 'depth': 1}
        for i, j in edges
    ]


class KCFGTestCase(TestCase):

    def test_from_dict_single_node(self):
        # Given
        d = {'nodes': node_dicts(1)}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(cfg.nodes, {node(0)})
        self.assertDictEqual(cfg.to_dict(), d)

    def test_from_dict_two_nodes(self):
        # Given
        d = {'nodes': node_dicts(2)}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(cfg.nodes, {node(0), node(1)})

    def test_from_dict_loop_edge(self):
        # Given
        d = {'nodes': node_dicts(1), 'edges': edge_dicts((0, 0))}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(cfg.nodes, {node(0)})
        self.assertSetEqual(cfg.edges(), {edge(0, 0)})
        self.assertEqual(cfg.edge(nid(0), nid(0)), edge(0, 0))
        self.assertDictEqual(cfg.to_dict(), d)

    def test_from_dict_simple_edge(self):
        # Given
        d = {'nodes': node_dicts(2), 'edges': edge_dicts((0, 1))}

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertSetEqual(cfg.nodes, {node(0), node(1)})
        self.assertSetEqual(cfg.edges(), {edge(0, 1)})
        self.assertEqual(cfg.edge(nid(0), nid(1)), edge(0, 1))

    def test_create_node(self):
        # Given
        cfg = KCFG()

        # When
        new_node = cfg.create_node(term(0))

        # Then
        self.assertEqual(new_node, node(0))
        self.assertSetEqual(cfg.nodes, {node(0)})

    def test_remove_unknown_node(self):
        # Given
        cfg = KCFG()

        # Then
        with self.assertRaises(ValueError):
            # When
            cfg.remove_node(nid(0))

    def test_remove_node(self):
        # Given
        d = {'nodes': node_dicts(1), 'edges': edge_dicts((0, 0))}
        cfg = KCFG.from_dict(d)

        # When
        cfg.remove_node(nid(0))

        # Then
        self.assertSetEqual(cfg.nodes, set())
        self.assertSetEqual(cfg.edges(), set())
        with self.assertRaises(ValueError):
            cfg.node(nid(0))
        with self.assertRaises(ValueError):
            cfg.edge(nid(0), nid(0))

    def test_insert_loop_edge(self):
        # Given
        d = {'nodes': node_dicts(1)}
        cfg = KCFG.from_dict(d)

        # When
        new_edge = cfg.create_edge(nid(0), nid(0))

        # Then
        self.assertEqual(new_edge, edge(0, 0))
        self.assertSetEqual(cfg.nodes, {node(0)})
        self.assertSetEqual(cfg.edges(), {edge(0, 0)})
        self.assertEqual(cfg.edge(nid(0), nid(0)), edge(0, 0))

    def test_insert_simple_edge(self):
        # Given
        d = {'nodes': node_dicts(2)}
        cfg = KCFG.from_dict(d)

        # When
        new_edge = cfg.create_edge(nid(0), nid(1))

        # Then
        self.assertEqual(new_edge, edge(0, 1))
        self.assertSetEqual(cfg.nodes, {node(0), node(1)})
        self.assertSetEqual(cfg.edges(), {edge(0, 1)})

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
            'nodes': node_dicts(6),
            'edges': edge_dicts((0, 1), (0, 5), (1, 2), (1, 3), (2, 4), (3, 4), (4, 1)),
        }
        cfg = KCFG.from_dict(d)

        # When
        nodes = set(cfg.reachable_nodes(nid(1)))

        # Then
        self.assertSetEqual(nodes, {node(1), node(2), node(3), node(4)})

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
