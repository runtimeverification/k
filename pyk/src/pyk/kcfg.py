import json
from abc import ABC
from dataclasses import dataclass
from functools import reduce
from itertools import chain
from threading import RLock
from typing import (
    Any,
    Container,
    Dict,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from graphviz import Digraph

from .cterm import CTerm
from .kast import TRUE, KInner, KRuleLike
from .kastManip import buildRule, mlAnd, simplifyBool, unsafeMlPredToBool
from .ktool import KPrint
from .rewrite import Subst
from .utils import compare_short_hashes, shorten_hashes


class KCFG(Container[Union['KCFG.Node', 'KCFG.Edge', 'KCFG.Cover']]):

    @dataclass(frozen=True)
    class Node:
        cterm: CTerm

        def __init__(self, cterm: CTerm):
            object.__setattr__(self, 'cterm', cterm)

        @property
        def id(self) -> str:
            return self.cterm.hash

        def to_dict(self) -> Dict[str, Any]:
            return {'id': self.id, 'term': self.cterm.term.to_dict()}

    class EdgeLike(ABC):
        source: 'KCFG.Node'
        target: 'KCFG.Node'

    @dataclass(frozen=True)
    class Edge(EdgeLike):
        source: 'KCFG.Node'
        target: 'KCFG.Node'
        condition: KInner = TRUE
        depth: int = 1

        def to_dict(self) -> Dict[str, Any]:
            return {'source': self.source.id, 'target': self.target.id, 'condition': self.condition.to_dict(), 'depth': self.depth}

        def to_rule(self, claim=False, priority=50) -> KRuleLike:
            sentence_id = f'BASIC-BLOCK-{self.source.id}-TO-{self.target.id}'
            init_term = mlAnd([self.source.cterm.term, self.condition])
            final_term = self.target.cterm.term
            rule, _ = buildRule(sentence_id, init_term, final_term, claim=claim, priority=priority)
            return rule

    @dataclass(frozen=True)
    class Cover(EdgeLike):
        source: 'KCFG.Node'
        target: 'KCFG.Node'
        subst: Subst
        constraint: KInner

        def __init__(self, source: 'KCFG.Node', target: 'KCFG.Node'):
            object.__setattr__(self, 'source', source)
            object.__setattr__(self, 'target', target)

            match_res = source.cterm.match_with_constraint(target.cterm)
            if not match_res:
                raise ValueError(f'No matching between: {source.id} and {target.id}')

            subst, constraint = match_res
            object.__setattr__(self, 'subst', subst)
            object.__setattr__(self, 'constraint', constraint)

        def to_dict(self) -> Dict[str, Any]:
            return {'source': self.source.id, 'target': self.target.id}

    _nodes: Dict[str, Node]
    _edges: Dict[str, Dict[str, Edge]]
    _covers: Dict[str, Dict[str, Cover]]
    _init: Set[str]
    _target: Set[str]
    _expanded: Set[str]
    _lock: RLock

    def __init__(self):
        self._nodes = {}
        self._edges = {}
        self._covers = {}
        self._init = set()
        self._target = set()
        self._expanded = set()
        self._lock = RLock()

    def __contains__(self, item: object) -> bool:
        if type(item) is KCFG.Node:
            return self.contains_node(item)
        if type(item) is KCFG.Edge:
            return self.contains_edge(item)
        if type(item) is KCFG.Cover:
            return self.contains_cover(item)
        return False

    def __enter__(self):
        self._lock.acquire()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self._lock.release()
        if exc_type is None:
            return True
        return False

    @property
    def nodes(self) -> List[Node]:
        return list(self._nodes.values())

    @property
    def init(self) -> List[Node]:
        return [node for node in self.nodes if self.is_init(node.id)]

    @property
    def target(self) -> List[Node]:
        return [node for node in self.nodes if self.is_target(node.id)]

    @property
    def expanded(self) -> List[Node]:
        return [node for node in self.nodes if self.is_expanded(node.id)]

    @property
    def leaves(self) -> List[Node]:
        return [node for node in self.nodes if self.is_leaf(node.id)]

    @property
    def covered(self) -> List[Node]:
        return [node for node in self.nodes if self.is_covered(node.id)]

    @property
    def uncovered(self) -> List[Node]:
        return [node for node in self.nodes if not self.is_covered(node.id)]

    @property
    def frontier(self) -> List[Node]:
        return [node for node in self.nodes if self.is_frontier(node.id)]

    @property
    def stuck(self) -> List[Node]:
        return [node for node in self.nodes if self.is_stuck(node.id)]

    def to_dict(self) -> Dict[str, Any]:
        nodes = [node.to_dict() for node in self.nodes]
        edges = [edge.to_dict() for edge in self.edges()]
        covers = [cover.to_dict() for cover in self.covers()]

        init = sorted(self._init)
        target = sorted(self._target)
        expanded = sorted(self._expanded)

        res = {
            'nodes': nodes,
            'edges': edges,
            'covers': covers,
            'init': init,
            'target': target,
            'expanded': expanded,
        }
        return {k: v for k, v in res.items() if v}

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'KCFG':
        cfg = KCFG()

        nodes: Dict[str, str] = {}

        def resolve(node_id: str) -> str:
            if node_id not in nodes:
                raise ValueError(f'Undeclared node: {node_id}')
            return nodes[node_id]

        for node_dict in dct.get('nodes') or []:
            cterm = CTerm(KInner.from_dict(node_dict['term']))
            node = cfg.create_node(cterm)

            node_key = node_dict['id']
            if node_key in nodes:
                raise ValueError(f'Multiple declarations of node: {node_key}')
            nodes[node_key] = node.id

        for edge_dict in dct.get('edges') or []:
            source_id = resolve(edge_dict['source'])
            target_id = resolve(edge_dict['target'])
            condition = KInner.from_dict(edge_dict['condition'])
            depth = edge_dict['depth']
            cfg.create_edge(source_id, target_id, condition, depth)

        for cover_dict in dct.get('covers') or []:
            source_id = resolve(cover_dict['source'])
            target_id = resolve(cover_dict['target'])
            cfg.create_cover(source_id, target_id)

        for init_id in dct.get('init') or []:
            cfg.add_init(resolve(init_id))

        for target_id in dct.get('target') or []:
            cfg.add_target(resolve(target_id))

        for expanded_id in dct.get('expanded') or []:
            cfg.add_expanded(resolve(expanded_id))

        return cfg

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True)

    @staticmethod
    def from_json(s: str) -> 'KCFG':
        return KCFG.from_dict(json.loads(s))

    def to_dot(self, kprint: KPrint) -> str:
        def _node_attrs(node_id: str) -> List[str]:
            atts = []
            if self.is_init(node_id):
                atts.append('init')
            if self.is_target(node_id):
                atts.append('target')
            if self.is_expanded(node_id):
                atts.append('expanded')
            if self.is_stuck(node_id):
                atts.append('stuck')
            if self.is_frontier(node_id):
                atts.append('frontier')
            return atts

        def _short_label(label):
            return '\n'.join([label_line if len(label_line) < 100 else (label_line[0:100] + ' ...') for label_line in label.split('\n')])

        graph = Digraph()

        for node in self.nodes:
            classAttrs = ' '.join(_node_attrs(node.id))
            label = shorten_hashes(node.id) + (classAttrs and ' ' + classAttrs)
            attrs = {'class': classAttrs} if classAttrs else {}
            graph.node(name=node.id, label=label, **attrs)

        for edge in self.edges():
            display_condition = simplifyBool(unsafeMlPredToBool(edge.condition))
            depth = edge.depth
            label = '\nandBool'.join(kprint.prettyPrint(display_condition).split(' andBool'))
            label = f'{label}\n{depth} steps'
            label = _short_label(label)
            graph.edge(tail_name=edge.source.id, head_name=edge.target.id, label=f'  {label}        ')

        for cover in self.covers():
            label = ', '.join(f'{k} |-> {kprint.prettyPrint(v)}' for k, v in cover.subst.items())
            label = _short_label(label)
            attrs = {'class': 'abstraction', 'style': 'dashed'}
            graph.edge(tail_name=cover.source.id, head_name=cover.target.id, label=f'  {label}        ', **attrs)

        for target in self._target:
            for node in self.frontier:
                attrs = {'class': 'target', 'style': 'solid'}
                graph.edge(tail_name=node.id, head_name=target, label='  ???', **attrs)

        return graph.source

    def _resolve_all(self, short_id: str) -> List[str]:
        return [node_id for node_id in self._nodes if compare_short_hashes(short_id, node_id)]

    def _resolve_or_none(self, short_id: str) -> Optional[str]:
        matches = self._resolve_all(short_id)
        if not matches:
            return None
        if len(matches) > 1:
            raise ValueError(f'Multiple nodes for pattern: {short_id} (matches e.g. {matches[0]} and {matches[1]})')
        return matches[0]

    def _resolve(self, short_id: str) -> str:
        match = self._resolve_or_none(short_id)
        if not match:
            raise ValueError(f'Unknown node: {short_id}')
        return match

    def node(self, node_id: str) -> Node:
        node_id = self._resolve(node_id)
        return self._nodes[node_id]

    def get_node(self, id: str) -> Optional[Node]:
        return self._nodes.get(id)

    def get_node_by_cterm(self, cterm: CTerm) -> Optional[Node]:
        node = KCFG.Node(cterm)
        return self.get_node(node.id)

    def contains_node(self, node: Node) -> bool:
        return bool(self.get_node(node.id))

    def create_node(self, cterm: CTerm) -> Node:
        node = KCFG.Node(cterm)

        if node.id in self._nodes:
            raise ValueError(f'Node already exists: {node.id}')

        self._nodes[node.id] = node
        return node

    def get_or_create_node(self, cterm: CTerm) -> Node:
        return self.get_node_by_cterm(cterm) or self.create_node(cterm)

    def remove_node(self, node_id: str) -> None:
        node_id = self._resolve(node_id)

        self._nodes.pop(node_id)

        self._edges.pop(node_id, None)
        for source_id in list(self._edges):
            self._edges[source_id].pop(node_id, None)
            if not self._edges[source_id]:
                self._edges.pop(source_id)

        self._covers.pop(node_id, None)
        for source_id in list(self._covers):
            self._covers[source_id].pop(node_id, None)
            if not self._covers[source_id]:
                self._covers.pop(source_id)

        self._init.discard(node_id)
        self._target.discard(node_id)
        self._expanded.discard(node_id)

    def edge(self, source_id: str, target_id: str) -> Optional[Edge]:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        return self._edges.get(source_id, {}).get(target_id)

    def edges(self, *, source_id: Optional[str] = None, target_id: Optional[str] = None) -> List[Edge]:
        source_id = self._resolve(source_id) if source_id is not None else None
        target_id = self._resolve(target_id) if target_id is not None else None

        res: Iterable[KCFG.Edge]
        if source_id:
            res = self._edges.get(source_id, {}).values()
        else:
            res = (edge for _, targets in self._edges.items() for _, edge in targets.items())

        return [edge for edge in res if not target_id or target_id == edge.target.id]

    def contains_edge(self, edge: Edge) -> bool:
        if other := self.edge(source_id=edge.source.id, target_id=edge.target.id):
            return edge == other
        return False

    def create_edge(self, source_id: str, target_id: str, condition: KInner = TRUE, depth=1) -> Edge:
        source = self.node(source_id)
        target = self.node(target_id)

        if target.id in self._edges.get(source.id, {}):
            raise ValueError(f'Edge already exists: {source.id} -> {target.id}')

        if source.id not in self._edges:
            self._edges[source.id] = {}

        edge = KCFG.Edge(source, target, condition, depth)
        self._edges[source.id][target.id] = edge
        return edge

    def remove_edge(self, source_id: str, target_id: str) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        edge = self.edge(source_id, target_id)

        if not edge:
            raise ValueError(f'Edge does not exist: {source_id} -> {target_id}')

        self._edges[source_id].pop(target_id)
        if not self._edges[source_id]:
            self._edges.pop(source_id)

    def cover(self, source_id: str, target_id: str) -> Optional[Cover]:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        return self._covers.get(source_id, {}).get(target_id)

    def covers(self, *, source_id: Optional[str] = None, target_id: Optional[str] = None) -> List[Cover]:
        source_id = self._resolve(source_id) if source_id is not None else None
        target_id = self._resolve(target_id) if target_id is not None else None

        res: Iterable[KCFG.Cover]
        if source_id:
            res = self._covers.get(source_id, {}).values()
        else:
            res = (cover for _, targets in self._covers.items() for _, cover in targets.items())

        return [cover for cover in res if not target_id or target_id == cover.target.id]

    def contains_cover(self, cover: Cover) -> bool:
        if other := self.cover(source_id=cover.source.id, target_id=cover.target.id):
            return cover == other
        return False

    def create_cover(self, source_id: str, target_id: str) -> Cover:
        source = self.node(source_id)
        target = self.node(target_id)

        if target.id in self._covers.get(source.id, {}):
            raise ValueError(f'Cover already exists: {source.id} -> {target.id}')

        if source.id not in self._covers:
            self._covers[source.id] = {}

        cover = KCFG.Cover(source, target)
        self._covers[source.id][target.id] = cover
        return cover

    def remove_cover(self, source_id: str, target_id: str) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        cover = self.cover(source_id, target_id)

        if not cover:
            raise ValueError(f'Cover does not exist: {source_id} -> {target_id}')

        self._covers[source_id].pop(target_id)
        if not self._covers[source_id]:
            self._covers.pop(source_id)

    def add_init(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._init.add(node_id)

    def add_target(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._target.add(node_id)

    def add_expanded(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._expanded.add(node_id)

    def remove_init(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        if node_id not in self._init:
            raise ValueError(f'Node is not init: {node_id}')
        self._init.remove(node_id)

    def remove_target(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        if node_id not in self._target:
            raise ValueError(f'Node is not target: {node_id}')
        self._target.remove(node_id)

    def remove_expanded(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        if node_id not in self._expanded:
            raise ValueError(f'Node is not expanded: {node_id}')
        self._expanded.remove(node_id)

    def discard_init(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._init.discard(node_id)

    def discard_target(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._target.discard(node_id)

    def discard_expanded(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._expanded.discard(node_id)

    def is_init(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._init

    def is_target(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._target

    def is_expanded(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._expanded

    def is_leaf(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return node_id not in self._edges

    def is_covered(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._covers

    def is_frontier(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return not any([self.is_target(node_id), self.is_expanded(node_id), self.is_covered(node_id)])

    def is_stuck(self, node_id: str) -> bool:
        node_id = self._resolve(node_id)
        return self.is_expanded(node_id) and self.is_leaf(node_id)

    def prune(self, node_id: str) -> None:
        nodes = self.reachable_nodes(node_id)
        for node in nodes:
            self.remove_node(node.id)

    def paths_between(self, source_id: str, target_id: str, *, traverse_covers=False) -> List[Tuple[EdgeLike, ...]]:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)

        INIT = 1
        POP_PATH = 2

        visited: Set[str] = set()
        path: List[KCFG.EdgeLike] = []
        paths: List[Tuple[KCFG.EdgeLike, ...]] = []

        worklist: List[Any] = [INIT]

        while worklist:
            item = worklist.pop()

            if type(item) == str:
                visited.remove(item)
                continue

            if item == POP_PATH:
                path.pop()
                continue

            node_id: str

            if item == INIT:
                node_id = source_id

            else:
                assert isinstance(item, KCFG.EdgeLike)

                node_id = item.target.id
                if node_id in visited:
                    continue

                path.append(item)

            if node_id == target_id:
                paths.append(tuple(path))
                continue

            visited.add(node_id)
            worklist.append(node_id)

            edges: List[KCFG.EdgeLike] = list(self.edges(source_id=node_id))
            if traverse_covers:
                edges += self.covers(source_id=node_id)

            for edge in edges:
                worklist.append(POP_PATH)
                worklist.append(edge)

        return paths

    def reachable_nodes(self, node_id: str, *, reverse=False, traverse_covers=False) -> Set[Node]:
        node = self.node(node_id)

        visited: Set[KCFG.Node] = set()
        worklist: List[KCFG.Node] = [node]

        while worklist:
            node = worklist.pop()

            if node in visited:
                continue

            visited.add(node)

            edges: Iterable[KCFG.EdgeLike]
            if not reverse:
                edges = chain(self.edges(source_id=node.id), self.covers(source_id=node_id) if traverse_covers else [])
                worklist.extend(edge.target for edge in edges)
            else:
                edges = chain(self.edges(target_id=node.id), self.covers(target_id=node.id) if traverse_covers else [])
                worklist.extend(edge.source for edge in edges)

        return visited


def path_condition(path: Sequence[KCFG.EdgeLike]) -> Tuple[KInner, Subst, int]:
    constraints: List[KInner] = []
    substitutions: List[Subst] = []
    depth = 0

    for edge in path:
        if type(edge) == KCFG.Edge:
            constraints.append(edge.condition)
            depth += edge.depth
        elif type(edge) == KCFG.Cover:
            substitutions.append(edge.subst)
        else:
            assert False

    substitution = reduce(Subst.compose, reversed(substitutions), Subst())
    return mlAnd(constraints), substitution, depth
