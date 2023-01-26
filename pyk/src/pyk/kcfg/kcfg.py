import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import reduce
from itertools import chain
from threading import RLock
from types import TracebackType
from typing import (
    Any,
    Callable,
    Container,
    Dict,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Type,
    Union,
    cast,
)

from graphviz import Digraph

from pyk.cterm import CTerm, build_claim, build_rule
from pyk.kast.inner import KInner, Subst
from pyk.kast.manip import (
    bool_to_ml_pred,
    extract_lhs,
    extract_rhs,
    ml_pred_to_bool,
    mlAnd,
    remove_source_attributes,
    rename_generated_vars,
    simplify_bool,
)
from pyk.kast.outer import KClaim, KDefinition, KRule
from pyk.ktool import KPrint
from pyk.prelude.ml import mlTop
from pyk.utils import add_indent, compare_short_hashes, shorten_hash


class KCFG(Container[Union['KCFG.Node', 'KCFG.Edge', 'KCFG.Cover']]):
    @dataclass(frozen=True, order=True)
    class Node:
        cterm: CTerm

        def __init__(self, cterm: CTerm):
            object.__setattr__(self, 'cterm', cterm)

        @property
        def id(self) -> str:
            return self.cterm.hash

        def to_dict(self) -> Dict[str, Any]:
            return {'id': self.id, 'term': self.cterm.kast.to_dict()}

    class EdgeLike(ABC):
        source: 'KCFG.Node'
        target: 'KCFG.Node'

        @abstractmethod
        def pretty(self, kprint: KPrint) -> Iterable[str]:
            ...

        def __lt__(self, other: Any) -> bool:
            if not isinstance(other, KCFG.EdgeLike):
                return NotImplemented
            return (self.source, self.target) < (other.source, other.target)

    @dataclass(frozen=True)
    class Edge(EdgeLike):
        source: 'KCFG.Node'
        target: 'KCFG.Node'
        condition: KInner
        depth: int

        def to_dict(self) -> Dict[str, Any]:
            return {
                'source': self.source.id,
                'target': self.target.id,
                'condition': self.condition.to_dict(),
                'depth': self.depth,
            }

        def to_rule(self, priority: int = 50) -> KRule:
            sentence_id = f'BASIC-BLOCK-{self.source.id}-TO-{self.target.id}'
            rule, _ = build_rule(
                sentence_id, self.source.cterm.add_constraint(self.condition), self.target.cterm, priority=priority
            )
            return rule

        def to_claim(self) -> KClaim:
            sentence_id = f'BASIC-BLOCK-{self.source.id}-TO-{self.target.id}'
            claim, _ = build_claim(sentence_id, self.source.cterm.add_constraint(self.condition), self.target.cterm)
            return claim

        def pretty(self, kprint: KPrint) -> Iterable[str]:
            if self.depth == 0:
                return ['\nandBool'.join(kprint.pretty_print(ml_pred_to_bool(self.condition)).split(' andBool'))]
            elif self.depth == 1:
                return ['(' + str(self.depth) + ' step)']
            else:
                return ['(' + str(self.depth) + ' steps)']

        # TODO: These should only be available for split case nodes and return a Node rather than a CTerm,
        # when we extract a class for them.
        def pre(self) -> CTerm:
            return self.source.cterm.add_constraint(self.condition)

        def post(self) -> CTerm:
            return self.target.cterm

    @dataclass(frozen=True)
    class Cover(EdgeLike):
        source: 'KCFG.Node'
        target: 'KCFG.Node'
        subst: Subst
        constraint: KInner

        def __init__(
            self,
            source: 'KCFG.Node',
            target: 'KCFG.Node',
            subst: Optional[Subst] = None,
            constraint: Optional[KInner] = None,
        ):
            object.__setattr__(self, 'source', source)
            object.__setattr__(self, 'target', target)

            if subst is None and constraint is not None:
                subst = Subst({})
            elif subst is not None and constraint is None:
                constraint = mlTop()
            elif subst is None and constraint is None:
                match_res = target.cterm.match_with_constraint(source.cterm)
                if not match_res:
                    raise ValueError(f'No matching between: {source.id} and {target.id}')
                subst, constraint = match_res

            object.__setattr__(self, 'subst', subst)
            object.__setattr__(self, 'constraint', constraint)

        def to_dict(self) -> Dict[str, Any]:
            return {
                'source': self.source.id,
                'target': self.target.id,
                'subst': self.subst.to_dict(),
                'constraint': self.constraint.to_dict(),
            }

        def pretty(self, kprint: KPrint, minimize: bool = True) -> Iterable[str]:
            subst_strs = [f'{k} <- {kprint.pretty_print(v)}' for k, v in self.subst.items()]
            subst_str = ''
            if len(subst_strs) == 0:
                subst_str = '.Subst'
            if len(subst_strs) == 1:
                subst_str = subst_strs[0]
            if len(subst_strs) > 1 and minimize:
                subst_str = 'OMITTED SUBST'
            if len(subst_strs) > 1 and not minimize:
                subst_str = '{\n    ' + '\n    '.join(subst_strs) + '\n}'
            constraint_str = kprint.pretty_print(ml_pred_to_bool(self.constraint, unsafe=True))
            if len(constraint_str) > 78:
                constraint_str = 'OMITTED CONSTRAINT'
            return [
                f'constraint: {constraint_str}',
                f'subst: {subst_str}',
            ]

    _nodes: Dict[str, Node]
    _edges: Dict[str, Dict[str, Edge]]
    _covers: Dict[str, Dict[str, Cover]]
    _init: Set[str]
    _target: Set[str]
    _expanded: Set[str]
    _verified: Set[Tuple[str, str]]
    _aliases: Dict[str, str]
    _lock: RLock

    def __init__(self) -> None:  # TODO should be unnecessary
        self._nodes = {}
        self._edges = {}
        self._covers = {}
        self._init = set()
        self._target = set()
        self._expanded = set()
        self._verified = set()
        self._aliases = {}
        self._lock = RLock()

    def __contains__(self, item: object) -> bool:
        if type(item) is KCFG.Node:
            return self.contains_node(item)
        if type(item) is KCFG.Edge:
            return self.contains_edge(item)
        if type(item) is KCFG.Cover:
            return self.contains_cover(item)
        return False

    def __enter__(self) -> 'KCFG':
        self._lock.acquire()
        return self

    def __exit__(
        self,
        exc_type: Optional[Type[BaseException]],
        exc_value: Optional[BaseException],
        traceback: Optional[TracebackType],
    ) -> bool:
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
    def verified(self) -> List[Edge]:
        return [edge for edge in self.edges() if self.is_verified(edge.source.id, edge.target.id)]

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

    @staticmethod
    def from_claim(defn: KDefinition, claim: KClaim) -> 'KCFG':
        cfg = KCFG()
        claim_body = claim.body
        claim_body = defn.instantiate_cell_vars(claim_body)
        claim_body = rename_generated_vars(claim_body)

        claim_lhs = CTerm(extract_lhs(claim_body)).add_constraint(bool_to_ml_pred(claim.requires))
        init_state = cfg.create_node(claim_lhs)
        cfg.add_init(init_state.id)

        claim_rhs = CTerm(extract_rhs(claim_body)).add_constraint(bool_to_ml_pred(claim.ensures))
        target_state = cfg.create_node(claim_rhs)
        cfg.add_target(target_state.id)

        return cfg

    def to_dict(self) -> Dict[str, Any]:
        nodes = [node.to_dict() for node in self.nodes]
        edges = [edge.to_dict() for edge in self.edges()]
        covers = [cover.to_dict() for cover in self.covers()]

        init = sorted(self._init)
        target = sorted(self._target)
        expanded = sorted(self._expanded)
        verified = [{'source': source_id, 'target': target_id} for source_id, target_id in sorted(self._verified)]
        aliases = dict(sorted(self._aliases.items()))

        res = {
            'nodes': nodes,
            'edges': edges,
            'covers': covers,
            'init': init,
            'target': target,
            'expanded': expanded,
            'verified': verified,
            'aliases': aliases,
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
            subst = None
            constraint = None
            if 'subst' in cover_dict:
                subst = Subst.from_dict(cover_dict['subst'])
            if 'constraint' in cover_dict:
                constraint = KInner.from_dict(cover_dict['constraint'])
            cfg.create_cover(source_id, target_id, subst=subst, constraint=constraint)

        for init_id in dct.get('init') or []:
            cfg.add_init(resolve(init_id))

        for target_id in dct.get('target') or []:
            cfg.add_target(resolve(target_id))

        for expanded_id in dct.get('expanded') or []:
            cfg.add_expanded(resolve(expanded_id))

        for verified_ids in dct.get('verified') or []:
            cfg.add_verified(resolve(verified_ids['source']), resolve(verified_ids['target']))

        for alias, id in dct.get('aliases', {}).items():
            cfg.add_alias(alias=alias, node_id=resolve(id))

        return cfg

    def aliases(self, node_id: str) -> List[str]:
        node_id = self._resolve(node_id)
        return [alias for alias, value in self._aliases.items() if node_id == value]

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True)

    @staticmethod
    def from_json(s: str) -> 'KCFG':
        return KCFG.from_dict(json.loads(s))

    def node_short_info(self, node: Node, node_printer: Optional[Callable[[CTerm], Iterable[str]]] = None) -> List[str]:
        attrs = self.node_attrs(node.id) + ['@' + alias for alias in sorted(self.aliases(node.id))]
        attr_string = ' (' + ', '.join(attrs) + ')' if attrs else ''
        node_header = shorten_hash(node.id) + attr_string
        node_strs = [node_header]
        if node_printer:
            node_strs.extend(f' {nl}' for nl in node_printer(node.cterm))
        return node_strs

    def pretty_segments(
        self, kprint: KPrint, minimize: bool = True, node_printer: Optional[Callable[[CTerm], Iterable[str]]] = None
    ) -> Iterable[Tuple[str, Iterable[str]]]:
        """Return a pretty version of the KCFG in segments.

        Each segment is a tuple of an identifier and a list of lines to be printed for that segment (Tuple[str, Iterable[str]).
        The identifier tells you whether that segment is for a given node, edge, or just pretty spacing ('unknown').
        This is useful for applications which want to pretty print in chunks, so that they can know which printed region corresponds to each node/edge.
        """

        processed_nodes: List[KCFG.Node] = []
        ret_lines: List[Tuple[str, List[str]]] = []

        def _bold(text: str) -> str:
            return '\033[1m' + text + '\033[0m'

        def _green(text: str) -> str:
            return '\033[32m' + text + '\033[0m'

        def _print_node(node: KCFG.Node) -> List[str]:
            short_info = self.node_short_info(node, node_printer=node_printer)
            if self.is_frontier(node.id):
                short_info[0] = _bold(short_info[0])
            return short_info

        def _print_subgraph(indent: str, curr_node: KCFG.Node, prior_on_trace: List[KCFG.Node]) -> None:

            edges_from = sorted(self.edge_likes(source_id=curr_node.id))
            if curr_node in processed_nodes:
                if not edges_from:
                    return
                ret_edge_lines = [(indent + '┊')]
                if curr_node in prior_on_trace:
                    ret_edge_lines.append(indent + '└╌ (looped back)')
                else:
                    ret_edge_lines.append(indent + '└╌ (continues as previously)')
                ret_lines.append(('unknown', ret_edge_lines))
                return
            processed_nodes.append(curr_node)

            num_children = len(edges_from)
            is_cover = num_children == 1 and isinstance(edges_from[0], KCFG.Cover)
            is_branch = num_children > 1
            if is_branch:
                ret_lines.append(('unknown', [indent + '│']))
            for i, edge_like in enumerate(edges_from):
                is_last_child = i == num_children - 1

                if not (is_branch or is_cover):
                    elbow = '├ ' if len(self.edge_likes(source_id=edge_like.target.id)) else '└ '
                    new_indent = ''
                    node_indent = '│ '
                elif is_last_child:
                    elbow = '└╌' if is_cover else '┗━'
                    new_indent = '   '
                    node_indent = '   │'
                else:
                    elbow = '┣━'
                    new_indent = '┃  '
                    node_indent = '┃  │'

                if isinstance(edge_like, KCFG.Edge) and edge_like.depth:
                    ret_edge_lines = [(indent + '│')]
                    if self.is_verified(edge_like.source.id, edge_like.target.id):
                        ret_edge_lines.append(indent + '│  ' + _bold(_green('(verified)')))
                    ret_edge_lines.extend(add_indent(indent + '│  ', edge_like.pretty(kprint)))
                    ret_lines.append((f'edge({edge_like.source.id},{edge_like.target.id})', ret_edge_lines))
                elif isinstance(edge_like, KCFG.Cover):
                    ret_edge_lines = [(indent + '┊')]
                    ret_edge_lines.extend(add_indent(indent + '┊  ', edge_like.pretty(kprint, minimize=minimize)))
                    ret_lines.append((f'cover({edge_like.source.id},{edge_like.target.id})', ret_edge_lines))

                target_strs = _print_node(edge_like.target)
                ret_node_lines = [(indent + elbow + ' ' + target_strs[0])]

                if isinstance(edge_like, KCFG.Edge) and edge_like.depth == 0:
                    first, *rest = edge_like.pretty(kprint)
                    ret_node_lines[-1] += '    ' + first
                    ret_node_lines.extend(add_indent(indent + new_indent + '       ' + len(target_strs[0]) * ' ', rest))

                ret_node_lines.extend(add_indent(indent + node_indent, target_strs[1:]))
                ret_lines.append((f'node({edge_like.target.id})', ret_node_lines))

                _print_subgraph(indent + new_indent, edge_like.target, prior_on_trace + [edge_like.source])

                if is_branch and not is_last_child:
                    ret_lines.append(('unknown', [indent + new_indent]))

        init = sorted(self.init)
        while init:
            init_strs = _print_node(init[0])
            ret_lines.append(('unknown', ['']))
            ret_init = [('┌  ' + init_strs[0])]
            ret_init.extend(add_indent('│  ', init_strs[1:]))
            ret_lines.append((f'node({init[0].id})', ret_init))
            _print_subgraph('', init[0], [init[0]])
            init = sorted(node for node in self.nodes if node not in processed_nodes)

        _ret_lines = []
        used_ids = []
        for id, seg_lines in ret_lines:
            suffix = ''
            counter = 0
            while f'{id}{suffix}' in used_ids:
                suffix = f'_{counter}'
                counter += 1
            new_id = f'{id}{suffix}'
            used_ids.append(new_id)
            _ret_lines.append((f'{new_id}', [l.rstrip() for l in seg_lines]))
        return _ret_lines

    def pretty(
        self, kprint: KPrint, minimize: bool = True, node_printer: Optional[Callable[[CTerm], Iterable[str]]] = None
    ) -> Iterable[str]:
        return (
            line
            for _, seg_lines in self.pretty_segments(kprint, minimize=minimize, node_printer=node_printer)
            for line in seg_lines
        )

    def to_dot(self, kprint: KPrint) -> str:
        def _short_label(label: str) -> str:
            return '\n'.join(
                [
                    label_line if len(label_line) < 100 else (label_line[0:100] + ' ...')
                    for label_line in label.split('\n')
                ]
            )

        graph = Digraph()

        for node in self.nodes:
            label = '\n'.join(self.node_short_info(node))
            class_attrs = ' '.join(self.node_attrs(node.id))
            attrs = {'class': class_attrs} if class_attrs else {}
            graph.node(name=node.id, label=label, **attrs)

        for edge in self.edges():
            display_condition = simplify_bool(ml_pred_to_bool(edge.condition))
            depth = edge.depth
            label = '\nandBool'.join(kprint.pretty_print(display_condition).split(' andBool'))
            label = f'{label}\n{depth} steps'
            label = _short_label(label)
            attrs = (
                {'class': 'verified'} if self.is_verified(edge.source.id, edge.target.id) else {'class': 'unverified'}
            )
            graph.edge(tail_name=edge.source.id, head_name=edge.target.id, label=f'  {label}        ', **attrs)

        for cover in self.covers():
            label = ', '.join(f'{k} |-> {kprint.pretty_print(v)}' for k, v in cover.subst.minimize().items())
            label = _short_label(label)
            attrs = {'class': 'abstraction', 'style': 'dashed'}
            graph.edge(tail_name=cover.source.id, head_name=cover.target.id, label=f'  {label}        ', **attrs)

        for target in self._target:
            for node in self.frontier:
                attrs = {'class': 'target', 'style': 'solid'}
                graph.edge(tail_name=node.id, head_name=target, label='  ???', **attrs)
            for node in self.stuck:
                attrs = {'class': 'target', 'style': 'solid'}
                graph.edge(tail_name=node.id, head_name=target, label='  false', **attrs)

        return graph.source

    def _resolve_hash(self, id_like: str) -> List[str]:
        return [node_id for node_id in self._nodes if compare_short_hashes(id_like, node_id)]

    def get_unique_init(self) -> Node:
        if len(self.init) > 1:
            raise ValueError(f'Multiple init nodes found: {[shorten_hash(n.id) for n in self.init]}')
        return self.init[0]

    def get_unique_target(self) -> Node:
        if len(self.target) > 1:
            raise ValueError(f'Multiple target nodes found: {[shorten_hash(n.id) for n in self.target]}')
        return self.target[0]

    def get_first_frontier(self) -> Node:
        if len(self.frontier) == 0:
            raise ValueError('No frontiers remaining!')
        return self.frontier[0]

    def _resolve_or_none(self, id_like: str) -> Optional[str]:
        if id_like == '#init':
            return self.get_unique_init().id
        if id_like == '#target':
            return self.get_unique_target().id
        if id_like == '#frontier':
            return self.get_first_frontier().id

        if id_like.startswith('@'):
            if id_like[1:] in self._aliases:
                return self._aliases[id_like[1:]]
            raise ValueError(f'Unknown alias: {id_like}')
        matches = self._resolve_hash(id_like)
        if not matches:
            return None
        if len(matches) > 1:
            raise ValueError(f'Multiple nodes for pattern: {id_like} (matches e.g. {matches[0]} and {matches[1]})')
        return matches[0]

    def _resolve(self, id_like: str) -> str:
        match = self._resolve_or_none(id_like)
        if not match:
            raise ValueError(f'Unknown node: {id_like}')
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
        term = cterm.kast
        term = remove_source_attributes(term)
        cterm = CTerm(term)
        node = KCFG.Node(cterm)

        if node.id in self._nodes:
            raise ValueError(f'Node already exists: {node.id}')

        self._nodes[node.id] = node
        return node

    def get_or_create_node(self, cterm: CTerm) -> Node:
        return self.get_node_by_cterm(cterm) or self.create_node(cterm)

    def remove_node(self, node_id: str) -> None:
        node_id = self._resolve(node_id)

        for edge_in in [edge.source for edge in self.edges(target_id=node_id)]:
            self.discard_expanded(edge_in.id)

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
        self._verified = {
            (source_id, target_id)
            for source_id, target_id in self._verified
            if source_id != node_id and target_id != node_id
        }

        for alias in [alias for alias, id in self._aliases.items() if id == node_id]:
            self.remove_alias(alias)

    def replace_node(self, node_id: str, new_cterm: CTerm) -> str:

        # Remove old node, record data
        node = self.node(node_id)
        in_edges = self.edges(target_id=node.id)
        out_edges = self.edges(source_id=node.id)
        in_covers = self.covers(target_id=node.id)
        out_covers = self.covers(source_id=node.id)
        init = self.is_init(node.id)
        target = self.is_target(node.id)
        expanded = self.is_expanded(node.id)
        in_expanded = {edge.source.id: self.is_expanded(edge.source.id) for edge in in_edges}
        self.remove_node(node.id)

        # Add the new, update data
        new_node = self.get_or_create_node(new_cterm)
        for in_edge in in_edges:
            self.create_edge(in_edge.source.id, new_node.id, in_edge.condition, in_edge.depth)
        for out_edge in out_edges:
            self.create_edge(new_node.id, out_edge.target.id, out_edge.condition, out_edge.depth)
        for in_cover in in_covers:
            self.create_cover(in_cover.source.id, new_node.id, subst=in_cover.subst, constraint=in_cover.constraint)
        for out_cover in out_covers:
            self.create_cover(new_node.id, out_cover.target.id, subst=in_cover.subst, constraint=in_cover.constraint)
        if init:
            self.add_init(new_node.id)
        if target:
            self.add_target(new_node.id)
        if expanded:
            self.add_expanded(new_node.id)
        for nid in in_expanded:
            if in_expanded[nid]:
                self.add_expanded(nid)

        return new_node.id

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

    def create_edge(self, source_id: str, target_id: str, condition: KInner, depth: int) -> Edge:
        source = self.node(source_id)
        target = self.node(target_id)

        if target.id in self._edges.get(source.id, {}):
            raise ValueError(f'Edge already exists: {source.id} -> {target.id}')

        if source.id not in self._edges:
            self._edges[source.id] = {}

        edge = KCFG.Edge(source, target, condition, depth)
        self._edges[source.id][target.id] = edge
        return edge

    def split_node(self, source_id: str, constraints: Iterable[KInner]) -> List[str]:

        source = self.node(source_id)

        def _add_case_edge(_constraint: KInner) -> str:
            _cterm = source.cterm.add_constraint(_constraint)
            _node = self.get_or_create_node(_cterm)
            self.create_edge(source.id, _node.id, _constraint, 0)
            self.add_verified(source.id, _node.id)
            return _node.id

        branch_node_ids = [_add_case_edge(constraint) for constraint in constraints]
        self.add_expanded(source.id)
        return branch_node_ids

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

    def create_cover(
        self, source_id: str, target_id: str, subst: Optional[Subst] = None, constraint: Optional[KInner] = None
    ) -> Cover:
        source = self.node(source_id)
        target = self.node(target_id)

        if target.id in self._covers.get(source.id, {}):
            raise ValueError(f'Cover already exists: {source.id} -> {target.id}')

        if source.id not in self._covers:
            self._covers[source.id] = {}

        cover = KCFG.Cover(source, target, subst=subst, constraint=constraint)
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

    def edge_likes(self, *, source_id: Optional[str] = None, target_id: Optional[str] = None) -> List[EdgeLike]:
        return cast(List[KCFG.EdgeLike], self.edges(source_id=source_id, target_id=target_id)) + cast(
            List[KCFG.EdgeLike], self.covers(source_id=source_id, target_id=target_id)
        )

    def add_init(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._init.add(node_id)

    def add_target(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._target.add(node_id)

    def add_expanded(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._expanded.add(node_id)

    def add_verified(self, source_id: str, target_id: str) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        self._verified.add((source_id, target_id))

    def add_alias(self, alias: str, node_id: str) -> None:
        if '@' in alias:
            raise ValueError('Alias may not contain "@"')
        if alias in self._aliases:
            raise ValueError(f'Duplicate alias: {alias}')
        node_id = self._resolve(node_id)
        self._aliases[alias] = node_id

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

    def remove_verified(self, source_id: str, target_id: str) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        if (source_id, target_id) not in self._verified:
            raise ValueError(f'Edge is not verified: {(source_id, target_id)}')
        self._verified.remove((source_id, target_id))

    def remove_alias(self, alias: str) -> None:
        if alias not in self._aliases:
            raise ValueError(f'Alias does not exist: {alias}')
        self._aliases.pop(alias)

    def discard_init(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._init.discard(node_id)

    def discard_target(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._target.discard(node_id)

    def discard_expanded(self, node_id: str) -> None:
        node_id = self._resolve(node_id)
        self._expanded.discard(node_id)

    def discard_verified(self, source_id: str, target_id: str) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        self._verified.discard((source_id, target_id))

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

    def is_verified(self, source_id: str, target_id: str) -> bool:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        return (source_id, target_id) in self._verified

    def node_attrs(self, node_id: str) -> List[str]:
        attrs = []
        if self.is_init(node_id):
            attrs.append('init')
        if self.is_target(node_id):
            attrs.append('target')
        if self.is_expanded(node_id):
            attrs.append('expanded')
        if self.is_stuck(node_id):
            attrs.append('stuck')
        if self.is_frontier(node_id):
            attrs.append('frontier')
        if self.is_leaf(node_id):
            attrs.append('leaf')
        return attrs

    def prune(self, node_id: str) -> None:
        nodes = self.reachable_nodes(node_id)
        for node in nodes:
            self.remove_node(node.id)

    def paths_between(
        self, source_id: str, target_id: str, *, traverse_covers: bool = False
    ) -> List[Tuple[EdgeLike, ...]]:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)

        INIT = 1  # noqa: N806
        POP_PATH = 2  # noqa: N806

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

    def reachable_nodes(self, source_id: str, *, reverse: bool = False, traverse_covers: bool = False) -> Set[Node]:

        visited: Set[KCFG.Node] = set()
        worklist: List[KCFG.Node] = [self.node(source_id)]

        while worklist:
            node = worklist.pop()

            if node in visited:
                continue

            visited.add(node)

            edges: Iterable[KCFG.EdgeLike]
            if not reverse:
                edges = chain(self.edges(source_id=node.id), self.covers(source_id=node.id) if traverse_covers else [])
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
            raise AssertionError

    substitution = reduce(Subst.compose, reversed(substitutions), Subst())
    return mlAnd(constraints), substitution, depth
