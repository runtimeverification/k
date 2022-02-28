from typing import Dict, Hashable, Iterable, Tuple, Union, cast
from unittest import TestCase

from ..kast import TOP, KInner
from ..kcfg import KCFG
from ..prelude import token


class KCFGTestCase(TestCase):

    def test_from_dict_single_state(self):
        # Given
        d = cfg_dict([(0, token(0))])

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertEqual(len(cfg.states), 1)
        self.assertEqual(cfg.states[0], token(0))

    def test_from_dict_two_states(self):
        # Given
        d = cfg_dict([(0, token(0)), (1, token(1))])

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertEqual(len(cfg.states), 2)
        self.assertEqual(cfg.states[0], token(0))
        self.assertEqual(cfg.states[1], token(1))

    def test_from_dict_loop_edge(self):
        # Given
        d = cfg_dict(states=[(0, token(0))], edges=[(0, token(True), 0)])

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertEqual(len(cfg.states), 1)
        self.assertEqual(cfg.states[0], token(0))
        self.assertEqual(len(cfg.graph), 1)
        self.assertEqual(len(cfg.graph[0]), 1)
        self.assertEqual(cfg.graph[0][0]['condition'], token(True))

    def test_from_dict_simple_edge(self):
        # Given
        d = cfg_dict(states=[(0, token(0)), (1, token(1))], edges=[(0, token(True), 1)])

        # When
        cfg = KCFG.from_dict(d)

        # Then
        self.assertEqual(len(cfg.states), 2)
        self.assertEqual(cfg.states[0], token(0))
        self.assertEqual(cfg.states[1], token(1))
        self.assertEqual(len(cfg.graph), 2)
        self.assertEqual(len(cfg.graph[0]), 1)
        self.assertEqual(cfg.graph[0][1]['condition'], token(True))
        self.assertDictEqual(cfg.graph[1], {})

    def test_insert_node(self):
        # Given
        cfg = KCFG()

        # When
        _, node_id = cfg.insertNode(token(True))

        # Then
        self.assertEqual(len(cfg.states), 1)
        self.assertEqual(cfg.states[node_id], token(True))

    def test_remove_unknown_node(self):
        # Given
        cfg = KCFG()

        # Then
        with self.assertRaises(ValueError):
            # When
            cfg.removeNode(0)

    def test_remove_node(self):
        # Given
        d = cfg_dict([0])
        cfg = KCFG.from_dict(d)

        # When
        cfg.removeNode(0)

        # Then
        self.assertEqual(len(cfg.states), 0)

    def test_insert_loop_edge(self):
        # Given
        d = cfg_dict([0])
        cfg = KCFG.from_dict(d)

        # When
        cfg.insertEdge(0, token(True), 0, depth=1)

        # Then
        self.assertEqual(len(cfg.graph), 1)

    def test_insert_simple_edge(self):
        # Given
        d = cfg_dict([0, 1])
        cfg = KCFG.from_dict(d)

        # When
        cfg.insertEdge(0, token(True), 1, depth=1)

        # Then
        self.assertEqual(len(cfg.graph), 2)
        self.assertEqual(len(cfg.graph[0]), 1)
        self.assertEqual(cfg.graph[0][1]['condition'], token(True))
        self.assertDictEqual(cfg.graph[1], {})

    def test_get_successors(self):
        d = cfg_dict(states=[0, 1, 2], edges=[(0, 1), (0, 2)])
        cfg = KCFG.from_dict(d)

        # When
        succs = set(cfg.getSuccessors(0))

        # Then
        self.assertSetEqual(succs, {1, 2})

    def test_get_predecessors(self):
        d = cfg_dict(states=[0, 1, 2], edges=[(0, 2), (1, 2)])
        cfg = KCFG.from_dict(d)

        # When
        preds = set(cfg.getPredecessors(2))

        # Then
        self.assertSetEqual(preds, {0, 1})

    def test_get_edges(self):
        d = cfg_dict(states=[0, 1, 2], edges=[(0, 1), (0, 2), (1, 2)])
        cfg = KCFG.from_dict(d)

        # When
        edges = set(cfg.getEdges())

        # Then
        self.assertSetEqual(edges, {(0, 1), (0, 2), (1, 2)})

    def test_transitive_closure(self):
        # Given
        d = cfg_dict(states=[0, 1, 2, 3, 4, 5], edges=[(0, 1), (0, 5), (1, 2), (1, 3), (2, 4), (3, 4), (4, 1)])
        cfg = KCFG.from_dict(d)

        # When
        node_ids = set(cfg.transitiveClosureFromState(1))

        # Then
        self.assertSetEqual(node_ids, {1, 2, 3, 4})

    def test_non_looping_paths_between_states(self):
        # Given
        d = cfg_dict(states=[0, 1, 2, 3], edges=[(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (3, 0)])
        cfg = KCFG.from_dict(d)

        # When
        paths = set(tuple(path) for path in cfg.nonLoopingPathsBetweenStates(0, 3))

        # Then
        self.assertSetEqual(paths, {(0, 1, 3), (0, 1, 2, 3), (0, 2, 3)})


def cfg_dict(
    states: Iterable[Union[Hashable, Tuple[Hashable, KInner]]],
    edges: Iterable[Union[Tuple[Hashable, Hashable], Tuple[Hashable, KInner, Hashable]]] = (),
) -> Dict:
    cfg_states = {}
    for state in states:
        state_key = state[0] if type(state) is tuple else state
        state_term = state[1] if type(state) is tuple else TOP
        cfg_states[state_key] = {'__kcfg_type__': 'k', **state_term.to_dict()}

    cfg_edges: Dict = {state: {} for state in cfg_states}
    for edge in edges:
        edge_src = edge[0]
        edge_term = cast(KInner, edge[1]) if len(edge) == 3 else TOP
        edge_trg = edge[-1]
        cfg_edges[edge_src][edge_trg] = {'depth': 1, 'condition': {'__kcfg_type__': 'k', **edge_term.to_dict()}, 'classes': [], 'priority': 50}

    return {'states': cfg_states, 'graph': cfg_edges}
