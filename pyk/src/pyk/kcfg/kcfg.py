from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from collections.abc import Container
from dataclasses import dataclass, field
from functools import reduce
from threading import RLock
from typing import TYPE_CHECKING, Final, List, Union, cast, final

from ..cterm import CSubst, CTerm, cterm_build_claim, cterm_build_rule
from ..kast import EMPTY_ATT
from ..kast.inner import KApply
from ..kast.manip import (
    bool_to_ml_pred,
    extract_lhs,
    extract_rhs,
    flatten_label,
    inline_cell_maps,
    rename_generated_vars,
    sort_ac_collections,
)
from ..kast.outer import KFlatModule
from ..prelude.kbool import andBool
from ..utils import ensure_dir_path, not_none, single

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping, MutableMapping
    from pathlib import Path
    from types import TracebackType
    from typing import Any

    from pyk.kore.rpc import LogEntry

    from ..kast import KAtt
    from ..kast.inner import KInner
    from ..kast.outer import KClaim, KDefinition, KImport, KRuleLike


NodeIdLike = int | str

_LOGGER: Final = logging.getLogger(__name__)


@dataclass(frozen=True)
class NodeAttr:
    value: str


class KCFGNodeAttr(NodeAttr):
    VACUOUS = NodeAttr('vacuous')
    STUCK = NodeAttr('stuck')


class KCFGStore:
    store_path: Path

    def __init__(self, store_path: Path) -> None:
        self.store_path = store_path
        ensure_dir_path(store_path)
        ensure_dir_path(self.kcfg_node_dir)

    @property
    def kcfg_json_path(self) -> Path:
        return self.store_path / 'kcfg.json'

    @property
    def kcfg_node_dir(self) -> Path:
        return self.store_path / 'nodes'

    def kcfg_node_path(self, node_id: int) -> Path:
        return self.kcfg_node_dir / f'{node_id}.json'

    def write_cfg_data(
        self, dct: dict[str, Any], deleted_nodes: Iterable[int] = (), created_nodes: Iterable[int] = ()
    ) -> None:
        node_dict = {node_dct['id']: node_dct for node_dct in dct['nodes']}
        vacuous_nodes = [
            node_id for node_id in node_dict.keys() if KCFGNodeAttr.VACUOUS.value in node_dict[node_id]['attrs']
        ]
        stuck_nodes = [
            node_id for node_id in node_dict.keys() if KCFGNodeAttr.STUCK.value in node_dict[node_id]['attrs']
        ]
        dct['vacuous'] = vacuous_nodes
        dct['stuck'] = stuck_nodes
        for node_id in deleted_nodes:
            self.kcfg_node_path(node_id).unlink(missing_ok=True)
        for node_id in created_nodes:
            del node_dict[node_id]['attrs']
            self.kcfg_node_path(node_id).write_text(json.dumps(node_dict[node_id]))
        dct['nodes'] = list(node_dict.keys())
        self.kcfg_json_path.write_text(json.dumps(dct))

    def read_cfg_data(self) -> dict[str, Any]:
        dct = json.loads(self.kcfg_json_path.read_text())
        nodes = [self.read_node_data(node_id) for node_id in dct.get('nodes') or []]
        dct['nodes'] = nodes

        new_nodes = []
        for node in dct['nodes']:
            attrs = []
            if node['id'] in dct['vacuous']:
                attrs.append(KCFGNodeAttr.VACUOUS.value)
            if node['id'] in dct['stuck']:
                attrs.append(KCFGNodeAttr.STUCK.value)
            new_nodes.append({'id': node['id'], 'cterm': node['cterm'], 'attrs': attrs})

        dct['nodes'] = new_nodes

        del dct['vacuous']
        del dct['stuck']

        return dct

    def read_node_data(self, node_id: int) -> dict[str, Any]:
        return json.loads(self.kcfg_node_path(node_id).read_text())


class KCFG(Container[Union['KCFG.Node', 'KCFG.Successor']]):
    @final
    @dataclass(frozen=True, order=True)
    class Node:
        id: int
        cterm: CTerm
        attrs: frozenset[NodeAttr]

        def __init__(self, id: int, cterm: CTerm, attrs: Iterable[NodeAttr] = ()) -> None:
            object.__setattr__(self, 'id', id)
            object.__setattr__(self, 'cterm', cterm)
            object.__setattr__(self, 'attrs', frozenset(attrs))

        def to_dict(self) -> dict[str, Any]:
            return {'id': self.id, 'cterm': self.cterm.to_dict(), 'attrs': [attr.value for attr in self.attrs]}

        @staticmethod
        def from_dict(dct: dict[str, Any]) -> KCFG.Node:
            return KCFG.Node(dct['id'], CTerm.from_dict(dct['cterm']), [NodeAttr(attr) for attr in dct['attrs']])

        def add_attr(self, attr: NodeAttr) -> KCFG.Node:
            return KCFG.Node(self.id, self.cterm, list(self.attrs) + [attr])

        def remove_attr(self, attr: NodeAttr) -> KCFG.Node:
            if attr not in self.attrs:
                raise ValueError(f'Node {self.id} does not have attribute {attr.value}')
            return KCFG.Node(self.id, self.cterm, self.attrs.difference([attr]))

        def discard_attr(self, attr: NodeAttr) -> KCFG.Node:
            return KCFG.Node(self.id, self.cterm, self.attrs.difference([attr]))

        def let(self, cterm: CTerm | None = None, attrs: Iterable[KCFGNodeAttr] | None = None) -> KCFG.Node:
            new_cterm = cterm if cterm is not None else self.cterm
            new_attrs = attrs if attrs is not None else self.attrs
            return KCFG.Node(self.id, new_cterm, new_attrs)

        @property
        def free_vars(self) -> frozenset[str]:
            return frozenset(self.cterm.free_vars)

    class Successor(ABC):
        source: KCFG.Node

        def __lt__(self, other: Any) -> bool:
            if not isinstance(other, KCFG.Successor):
                return NotImplemented
            return self.source < other.source

        @property
        def source_vars(self) -> frozenset[str]:
            return frozenset(self.source.free_vars)

        @property
        @abstractmethod
        def targets(self) -> tuple[KCFG.Node, ...]: ...

        @property
        def target_ids(self) -> list[int]:
            return sorted(target.id for target in self.targets)

        @property
        def target_vars(self) -> frozenset[str]:
            return frozenset(set.union(set(), *(target.free_vars for target in self.targets)))

        @abstractmethod
        def replace_source(self, node: KCFG.Node) -> KCFG.Successor: ...

        @abstractmethod
        def replace_target(self, node: KCFG.Node) -> KCFG.Successor: ...

        @abstractmethod
        def to_dict(self) -> dict[str, Any]: ...

        @staticmethod
        @abstractmethod
        def from_dict(dct: dict[str, Any], nodes: Mapping[int, KCFG.Node]) -> KCFG.Successor: ...

    class EdgeLike(Successor):
        source: KCFG.Node
        target: KCFG.Node

        @property
        def targets(self) -> tuple[KCFG.Node, ...]:
            return (self.target,)

    @final
    @dataclass(frozen=True)
    class Edge(EdgeLike):
        source: KCFG.Node
        target: KCFG.Node
        depth: int
        rules: tuple[str, ...]

        def to_dict(self) -> dict[str, Any]:
            return {
                'source': self.source.id,
                'target': self.target.id,
                'depth': self.depth,
                'rules': list(self.rules),
            }

        @staticmethod
        def from_dict(dct: dict[str, Any], nodes: Mapping[int, KCFG.Node]) -> KCFG.Edge:
            return KCFG.Edge(nodes[dct['source']], nodes[dct['target']], dct['depth'], tuple(dct['rules']))

        def to_rule(self, label: str, claim: bool = False, priority: int | None = None) -> KRuleLike:
            def is_ceil_condition(kast: KInner) -> bool:
                return type(kast) is KApply and kast.label.name == '#Ceil'

            def _simplify_config(config: KInner) -> KInner:
                return sort_ac_collections(inline_cell_maps(config))

            sentence_id = f'{label}-{self.source.id}-TO-{self.target.id}'
            init_constraints = [c for c in self.source.cterm.constraints if not is_ceil_condition(c)]
            init_cterm = CTerm(_simplify_config(self.source.cterm.config), init_constraints)
            target_constraints = [c for c in self.target.cterm.constraints if not is_ceil_condition(c)]
            target_cterm = CTerm(_simplify_config(self.target.cterm.config), target_constraints)
            rule: KRuleLike
            if claim:
                rule, _ = cterm_build_claim(sentence_id, init_cterm, target_cterm)
            else:
                rule, _ = cterm_build_rule(sentence_id, init_cterm, target_cterm, priority=priority)
            return rule

        def replace_source(self, node: KCFG.Node) -> KCFG.Edge:
            assert node.id == self.source.id
            return KCFG.Edge(node, self.target, self.depth, self.rules)

        def replace_target(self, node: KCFG.Node) -> KCFG.Edge:
            assert node.id == self.target.id
            return KCFG.Edge(self.source, node, self.depth, self.rules)

    @final
    @dataclass(frozen=True)
    class Cover(EdgeLike):
        source: KCFG.Node
        target: KCFG.Node
        csubst: CSubst

        def to_dict(self) -> dict[str, Any]:
            return {
                'source': self.source.id,
                'target': self.target.id,
                'csubst': self.csubst.to_dict(),
            }

        @staticmethod
        def from_dict(dct: dict[str, Any], nodes: Mapping[int, KCFG.Node]) -> KCFG.Cover:
            return KCFG.Cover(nodes[dct['source']], nodes[dct['target']], CSubst.from_dict(dct['csubst']))

        def replace_source(self, node: KCFG.Node) -> KCFG.Cover:
            assert node.id == self.source.id
            return KCFG.Cover(node, self.target, self.csubst)

        def replace_target(self, node: KCFG.Node) -> KCFG.Cover:
            assert node.id == self.target.id
            return KCFG.Cover(self.source, node, self.csubst)

    @dataclass(frozen=True)
    class MultiEdge(Successor):
        source: KCFG.Node

        def __lt__(self, other: Any) -> bool:
            if not type(other) is type(self):
                return NotImplemented
            return (self.source, self.target_ids) < (other.source, other.target_ids)

        @abstractmethod
        def with_single_target(self, target: KCFG.Node) -> KCFG.MultiEdge: ...

    @final
    @dataclass(frozen=True)
    class Split(MultiEdge):
        source: KCFG.Node
        _targets: tuple[tuple[KCFG.Node, CSubst], ...]

        def __init__(self, source: KCFG.Node, _targets: Iterable[tuple[KCFG.Node, CSubst]]) -> None:
            object.__setattr__(self, 'source', source)
            object.__setattr__(self, '_targets', tuple(_targets))

        @property
        def targets(self) -> tuple[KCFG.Node, ...]:
            return tuple(target for target, _ in self._targets)

        @property
        def splits(self) -> dict[int, CSubst]:
            return {target.id: csubst for target, csubst in self._targets}

        def to_dict(self) -> dict[str, Any]:
            return {
                'source': self.source.id,
                'targets': [
                    {
                        'target': target.id,
                        'csubst': csubst.to_dict(),
                    }
                    for target, csubst in self._targets
                ],
            }

        @staticmethod
        def from_dict(dct: dict[str, Any], nodes: Mapping[int, KCFG.Node]) -> KCFG.Split:
            _targets = [(nodes[target['target']], CSubst.from_dict(target['csubst'])) for target in dct['targets']]
            return KCFG.Split(nodes[dct['source']], tuple(_targets))

        def with_single_target(self, target: KCFG.Node) -> KCFG.Split:
            return KCFG.Split(self.source, ((target, self.splits[target.id]),))

        @property
        def covers(self) -> tuple[KCFG.Cover, ...]:
            return tuple(KCFG.Cover(target, self.source, csubst) for target, csubst in self._targets)

        def replace_source(self, node: KCFG.Node) -> KCFG.Split:
            assert node.id == self.source.id
            return KCFG.Split(node, self._targets)

        def replace_target(self, node: KCFG.Node) -> KCFG.Split:
            assert node.id in self.target_ids
            new_targets = [
                (node, csubst) if node.id == target_node.id else (target_node, csubst)
                for target_node, csubst in self._targets
            ]
            return KCFG.Split(self.source, tuple(new_targets))

    @final
    @dataclass(frozen=True)
    class NDBranch(MultiEdge):
        source: KCFG.Node
        _targets: tuple[KCFG.Node, ...]
        rules: tuple[str, ...]

        def __init__(self, source: KCFG.Node, _targets: Iterable[KCFG.Node], rules: tuple[str, ...]) -> None:
            object.__setattr__(self, 'source', source)
            object.__setattr__(self, '_targets', tuple(_targets))
            object.__setattr__(self, 'rules', rules)

        @property
        def targets(self) -> tuple[KCFG.Node, ...]:
            return self._targets

        def to_dict(self) -> dict[str, Any]:
            return {
                'source': self.source.id,
                'targets': [target.id for target in self.targets],
                'rules': list(self.rules),
            }

        @staticmethod
        def from_dict(dct: dict[str, Any], nodes: Mapping[int, KCFG.Node]) -> KCFG.NDBranch:
            return KCFG.NDBranch(
                nodes[dct['source']], tuple([nodes[target] for target in dct['targets']]), tuple(dct['rules'])
            )

        def with_single_target(self, target: KCFG.Node) -> KCFG.NDBranch:
            return KCFG.NDBranch(self.source, (target,), ())

        @property
        def edges(self) -> tuple[KCFG.Edge, ...]:
            return tuple(KCFG.Edge(self.source, target, 1, ()) for target in self.targets)

        def replace_source(self, node: KCFG.Node) -> KCFG.NDBranch:
            assert node.id == self.source.id
            return KCFG.NDBranch(node, self._targets, self.rules)

        def replace_target(self, node: KCFG.Node) -> KCFG.NDBranch:
            assert node.id in self.target_ids
            new_targets = [node if node.id == target_node.id else target_node for target_node in self._targets]
            return KCFG.NDBranch(self.source, tuple(new_targets), self.rules)

    _node_id: int
    _nodes: MutableMapping[int, KCFG.Node]

    _created_nodes: set[int]
    _deleted_nodes: set[int]

    _edges: dict[int, Edge]
    _covers: dict[int, Cover]
    _splits: dict[int, Split]
    _ndbranches: dict[int, NDBranch]
    _aliases: dict[str, int]
    _lock: RLock

    _kcfg_store: KCFGStore | None

    def __init__(self, cfg_dir: Path | None = None, optimize_memory: bool = True) -> None:
        self._node_id = 1
        if optimize_memory:
            from .store import OptimizedNodeStore

            self._nodes = OptimizedNodeStore()
        else:
            self._nodes = {}
        self._created_nodes = set()
        self._deleted_nodes = set()
        self._edges = {}
        self._covers = {}
        self._splits = {}
        self._ndbranches = {}
        self._aliases = {}
        self._lock = RLock()
        if cfg_dir is not None:
            self._kcfg_store = KCFGStore(cfg_dir)

    def __contains__(self, item: object) -> bool:
        if type(item) is KCFG.Node:
            return self.contains_node(item)
        if type(item) is KCFG.Edge:
            return self.contains_edge(item)
        if type(item) is KCFG.Cover:
            return self.contains_cover(item)
        if type(item) is KCFG.Split:
            return self.contains_split(item)
        if type(item) is KCFG.NDBranch:
            return self.contains_ndbranch(item)
        return False

    def __enter__(self) -> KCFG:
        self._lock.acquire()
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> bool:
        self._lock.release()
        if exc_type is None:
            return True
        return False

    @property
    def nodes(self) -> list[KCFG.Node]:
        return list(self._nodes.values())

    @property
    def root(self) -> list[KCFG.Node]:
        return [node for node in self.nodes if self.is_root(node.id)]

    @property
    def vacuous(self) -> list[KCFG.Node]:
        return [node for node in self.nodes if self.is_vacuous(node.id)]

    @property
    def stuck(self) -> list[KCFG.Node]:
        return [node for node in self.nodes if self.is_stuck(node.id)]

    @property
    def leaves(self) -> list[KCFG.Node]:
        return [node for node in self.nodes if self.is_leaf(node.id)]

    @property
    def covered(self) -> list[KCFG.Node]:
        return [node for node in self.nodes if self.is_covered(node.id)]

    @property
    def uncovered(self) -> list[KCFG.Node]:
        return [node for node in self.nodes if not self.is_covered(node.id)]

    @staticmethod
    def from_claim(
        defn: KDefinition, claim: KClaim, cfg_dir: Path | None = None, optimize_memory: bool = True
    ) -> tuple[KCFG, NodeIdLike, NodeIdLike]:
        cfg = KCFG(cfg_dir=cfg_dir, optimize_memory=optimize_memory)
        claim_body = claim.body
        claim_body = defn.instantiate_cell_vars(claim_body)
        claim_body = rename_generated_vars(claim_body)

        claim_lhs = CTerm.from_kast(extract_lhs(claim_body)).add_constraint(bool_to_ml_pred(claim.requires))
        init_node = cfg.create_node(claim_lhs)

        claim_rhs = CTerm.from_kast(extract_rhs(claim_body)).add_constraint(
            bool_to_ml_pred(andBool([claim.requires, claim.ensures]))
        )
        target_node = cfg.create_node(claim_rhs)

        return cfg, init_node.id, target_node.id

    @staticmethod
    def path_length(_path: Iterable[KCFG.Successor]) -> int:
        _path = tuple(_path)
        if len(_path) == 0:
            return 0
        if type(_path[0]) is KCFG.Split or type(_path[0]) is KCFG.Cover:
            return KCFG.path_length(_path[1:])
        elif type(_path[0]) is KCFG.NDBranch:
            return 1 + KCFG.path_length(_path[1:])
        elif type(_path[0]) is KCFG.Edge:
            return _path[0].depth + KCFG.path_length(_path[1:])
        raise ValueError(f'Cannot handle Successor type: {type(_path[0])}')

    def extend(
        self,
        extend_result: KCFGExtendResult,
        node: KCFG.Node,
        logs: dict[int, tuple[LogEntry, ...]],
    ) -> None:
        match extend_result:
            case Vacuous():
                self.add_vacuous(node.id)

            case Stuck():
                self.add_stuck(node.id)

            case Abstract(cterm):
                new_node = self.create_node(cterm)
                self.create_cover(node.id, new_node.id)

            case Step(cterm, depth, next_node_logs, rule_labels, _):
                next_node = self.create_node(cterm)
                logs[next_node.id] = next_node_logs
                self.create_edge(node.id, next_node.id, depth, rules=rule_labels)

            case Branch(constraints, _):
                self.split_on_constraints(node.id, constraints)

            case NDBranch(cterms, next_node_logs, rule_labels):
                next_ids = [self.create_node(cterm).id for cterm in cterms]
                for i in next_ids:
                    logs[i] = next_node_logs
                self.create_ndbranch(node.id, next_ids, rules=rule_labels)

            case _:
                raise AssertionError()

    def to_dict(self) -> dict[str, Any]:
        nodes = [node.to_dict() for node in self.nodes]
        edges = [edge.to_dict() for edge in self.edges()]
        covers = [cover.to_dict() for cover in self.covers()]
        splits = [split.to_dict() for split in self.splits()]
        ndbranches = [ndbranch.to_dict() for ndbranch in self.ndbranches()]

        aliases = dict(sorted(self._aliases.items()))

        res = {
            'next': self._node_id,
            'nodes': nodes,
            'edges': edges,
            'covers': covers,
            'splits': splits,
            'ndbranches': ndbranches,
            'aliases': aliases,
        }
        return {k: v for k, v in res.items() if v}

    @staticmethod
    def from_dict(dct: Mapping[str, Any], optimize_memory: bool = True) -> KCFG:
        cfg = KCFG(optimize_memory=optimize_memory)

        for node_dict in dct.get('nodes') or []:
            node = KCFG.Node.from_dict(node_dict)
            cfg.add_node(node)

        max_id = max([node.id for node in cfg.nodes], default=0)
        cfg._node_id = dct.get('next', max_id + 1)

        for edge_dict in dct.get('edges') or []:
            edge = KCFG.Edge.from_dict(edge_dict, cfg._nodes)
            cfg.add_successor(edge)

        for cover_dict in dct.get('covers') or []:
            cover = KCFG.Cover.from_dict(cover_dict, cfg._nodes)
            cfg.add_successor(cover)

        for split_dict in dct.get('splits') or []:
            split = KCFG.Split.from_dict(split_dict, cfg._nodes)
            cfg.add_successor(split)

        for ndbranch_dict in dct.get('ndbranches') or []:
            ndbranch = KCFG.NDBranch.from_dict(ndbranch_dict, cfg._nodes)
            cfg.add_successor(ndbranch)

        for alias, node_id in dct.get('aliases', {}).items():
            cfg.add_alias(alias=alias, node_id=node_id)

        return cfg

    def aliases(self, node_id: NodeIdLike) -> list[str]:
        node_id = self._resolve(node_id)
        return [alias for alias, value in self._aliases.items() if node_id == value]

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), sort_keys=True)

    @staticmethod
    def from_json(s: str, optimize_memory: bool = True) -> KCFG:
        return KCFG.from_dict(json.loads(s), optimize_memory=optimize_memory)

    def to_rules(self, priority: int = 20, id: str | None = None) -> list[KRuleLike]:
        id = '' if id is None else f'{id}-'
        return [e.to_rule(f'{id}BASIC-BLOCK', priority=priority) for e in self.edges()]

    def to_module(
        self,
        module_name: str | None = None,
        imports: Iterable[KImport] = (),
        priority: int = 20,
        att: KAtt = EMPTY_ATT,
    ) -> KFlatModule:
        module_name = 'KCFG' if module_name is None else module_name
        return KFlatModule(module_name, self.to_rules(priority=priority), imports=imports, att=att)

    def _resolve_or_none(self, id_like: NodeIdLike) -> int | None:
        if type(id_like) is int:
            if id_like in self._nodes:
                return id_like

            return None

        if type(id_like) is not str:
            raise TypeError(f'Expected int or str for id_like, got: {id_like}')

        if id_like.startswith('@'):
            if id_like[1:] in self._aliases:
                return self._aliases[id_like[1:]]
            raise ValueError(f'Unknown alias: {id_like}')

        return None

    def _resolve(self, id_like: NodeIdLike) -> int:
        match = self._resolve_or_none(id_like)
        if not match:
            raise ValueError(f'Unknown node: {id_like}')
        return match

    def node(self, node_id: NodeIdLike) -> KCFG.Node:
        node_id = self._resolve(node_id)
        return self._nodes[node_id]

    def get_node(self, node_id: NodeIdLike) -> KCFG.Node | None:
        resolved_id = self._resolve_or_none(node_id)
        if resolved_id is None:
            return None
        return self._nodes[resolved_id]

    def contains_node(self, node: KCFG.Node) -> bool:
        return bool(self.get_node(node.id))

    def add_node(self, node: KCFG.Node) -> None:
        if node.id in self._nodes:
            raise ValueError(f'Node with id already exists: {node.id}')
        self._nodes[node.id] = node
        self._created_nodes.add(node.id)

    def create_node(self, cterm: CTerm) -> KCFG.Node:
        node = KCFG.Node(self._node_id, cterm)
        self._node_id += 1
        self._nodes[node.id] = node
        self._created_nodes.add(node.id)
        return node

    def remove_node(self, node_id: NodeIdLike) -> None:
        node_id = self._resolve(node_id)

        node = self._nodes.pop(node_id)
        self._created_nodes.discard(node_id)
        self._deleted_nodes.add(node.id)

        self._edges = {k: s for k, s in self._edges.items() if k != node_id and node_id not in s.target_ids}
        self._covers = {k: s for k, s in self._covers.items() if k != node_id and node_id not in s.target_ids}

        self._splits = {k: s for k, s in self._splits.items() if k != node_id and node_id not in s.target_ids}
        self._ndbranches = {k: b for k, b in self._ndbranches.items() if k != node_id and node_id not in b.target_ids}

        for alias in [alias for alias, id in self._aliases.items() if id == node_id]:
            self.remove_alias(alias)

    def _update_refs(self, node_id: int) -> None:
        node = self.node(node_id)
        for succ in self.successors(node_id):
            new_succ = succ.replace_source(node)
            if type(new_succ) is KCFG.Edge:
                self._edges[new_succ.source.id] = new_succ
            if type(new_succ) is KCFG.Cover:
                self._covers[new_succ.source.id] = new_succ
            if type(new_succ) is KCFG.Split:
                self._splits[new_succ.source.id] = new_succ
            if type(new_succ) is KCFG.NDBranch:
                self._ndbranches[new_succ.source.id] = new_succ

        for pred in self.predecessors(node_id):
            new_pred = pred.replace_target(node)
            if type(new_pred) is KCFG.Edge:
                self._edges[new_pred.source.id] = new_pred
            if type(new_pred) is KCFG.Cover:
                self._covers[new_pred.source.id] = new_pred
            if type(new_pred) is KCFG.Split:
                self._splits[new_pred.source.id] = new_pred
            if type(new_pred) is KCFG.NDBranch:
                self._ndbranches[new_pred.source.id] = new_pred

    def remove_attr(self, node_id: NodeIdLike, attr: NodeAttr) -> None:
        node = self.node(node_id)
        new_node = node.remove_attr(attr)
        self.replace_node(new_node)

    def discard_attr(self, node_id: NodeIdLike, attr: NodeAttr) -> None:
        node = self.node(node_id)
        new_node = node.discard_attr(attr)
        self.replace_node(new_node)

    def add_attr(self, node_id: NodeIdLike, attr: NodeAttr) -> None:
        node = self.node(node_id)
        new_node = node.add_attr(attr)
        self.replace_node(new_node)

    def let_node(
        self, node_id: NodeIdLike, cterm: CTerm | None = None, attrs: Iterable[KCFGNodeAttr] | None = None
    ) -> None:
        node = self.node(node_id)
        new_node = node.let(cterm=cterm, attrs=attrs)
        self.replace_node(new_node)

    def replace_node(self, node: KCFG.Node) -> None:
        self._nodes[node.id] = node
        self._created_nodes.add(node.id)
        self._update_refs(node.id)

    def successors(self, source_id: NodeIdLike) -> list[Successor]:
        out_edges: Iterable[KCFG.Successor] = self.edges(source_id=source_id)
        out_covers: Iterable[KCFG.Successor] = self.covers(source_id=source_id)
        out_splits: Iterable[KCFG.Successor] = self.splits(source_id=source_id)
        out_ndbranches: Iterable[KCFG.Successor] = self.ndbranches(source_id=source_id)
        return list(out_edges) + list(out_covers) + list(out_splits) + list(out_ndbranches)

    def predecessors(self, target_id: NodeIdLike) -> list[Successor]:
        in_edges: Iterable[KCFG.Successor] = self.edges(target_id=target_id)
        in_covers: Iterable[KCFG.Successor] = self.covers(target_id=target_id)
        in_splits: Iterable[KCFG.Successor] = self.splits(target_id=target_id)
        in_ndbranches: Iterable[KCFG.Successor] = self.ndbranches(target_id=target_id)
        return list(in_edges) + list(in_covers) + list(in_splits) + list(in_ndbranches)

    def _check_no_successors(self, source_id: NodeIdLike) -> None:
        if len(self.successors(source_id)) > 0:
            raise ValueError(f'Node already has successors: {source_id} -> {self.successors(source_id)}')

    def _check_no_zero_loops(self, source_id: NodeIdLike, target_ids: Iterable[NodeIdLike]) -> None:
        for target_id in target_ids:
            path = self.shortest_path_between(target_id, source_id)
            if path is not None and KCFG.path_length(path) == 0:
                raise ValueError(
                    f'Adding successor would create zero-length loop with backedge: {source_id} -> {target_id}'
                )

    def add_successor(self, succ: KCFG.Successor) -> None:
        self._check_no_successors(succ.source.id)
        self._check_no_zero_loops(succ.source.id, succ.target_ids)
        if type(succ) is KCFG.Edge:
            self._edges[succ.source.id] = succ
        elif type(succ) is KCFG.Cover:
            self._covers[succ.source.id] = succ
        else:
            if len(succ.target_ids) <= 1:
                raise ValueError(
                    f'Cannot create {type(succ)} node with less than 2 targets: {succ.source.id} -> {succ.target_ids}'
                )
            if type(succ) is KCFG.Split:
                self._splits[succ.source.id] = succ
            elif type(succ) is KCFG.NDBranch:
                self._ndbranches[succ.source.id] = succ

    def edge(self, source_id: NodeIdLike, target_id: NodeIdLike) -> Edge | None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        edge = self._edges.get(source_id, None)
        return edge if edge is not None and edge.target.id == target_id else None

    def edges(self, *, source_id: NodeIdLike | None = None, target_id: NodeIdLike | None = None) -> list[Edge]:
        source_id = self._resolve(source_id) if source_id is not None else None
        target_id = self._resolve(target_id) if target_id is not None else None
        return [
            edge
            for edge in self._edges.values()
            if (source_id is None or source_id == edge.source.id) and (target_id is None or target_id == edge.target.id)
        ]

    def contains_edge(self, edge: Edge) -> bool:
        if other := self.edge(source_id=edge.source.id, target_id=edge.target.id):
            return edge == other
        return False

    def create_edge(self, source_id: NodeIdLike, target_id: NodeIdLike, depth: int, rules: Iterable[str] = ()) -> Edge:
        if depth <= 0:
            raise ValueError(f'Cannot build KCFG Edge with non-positive depth: {depth}')
        source = self.node(source_id)
        target = self.node(target_id)
        edge = KCFG.Edge(source, target, depth, tuple(rules))
        self.add_successor(edge)
        return edge

    def remove_edge(self, source_id: NodeIdLike, target_id: NodeIdLike) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        edge = self.edge(source_id, target_id)
        if not edge:
            raise ValueError(f'Edge does not exist: {source_id} -> {target_id}')
        self._edges.pop(source_id)

    def cover(self, source_id: NodeIdLike, target_id: NodeIdLike) -> Cover | None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        cover = self._covers.get(source_id, None)
        return cover if cover is not None and cover.target.id == target_id else None

    def covers(self, *, source_id: NodeIdLike | None = None, target_id: NodeIdLike | None = None) -> list[Cover]:
        source_id = self._resolve(source_id) if source_id is not None else None
        target_id = self._resolve(target_id) if target_id is not None else None
        return [
            cover
            for cover in self._covers.values()
            if (source_id is None or source_id == cover.source.id)
            and (target_id is None or target_id == cover.target.id)
        ]

    def contains_cover(self, cover: Cover) -> bool:
        if other := self.cover(source_id=cover.source.id, target_id=cover.target.id):
            return cover == other
        return False

    def create_cover(self, source_id: NodeIdLike, target_id: NodeIdLike, csubst: CSubst | None = None) -> Cover:
        source = self.node(source_id)
        target = self.node(target_id)
        if csubst is None:
            csubst = target.cterm.match_with_constraint(source.cterm)
            if csubst is None:
                raise ValueError(f'No matching between: {source.id} and {target.id}')
        cover = KCFG.Cover(source, target, csubst=csubst)
        self.add_successor(cover)
        return cover

    def remove_cover(self, source_id: NodeIdLike, target_id: NodeIdLike) -> None:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)
        cover = self.cover(source_id, target_id)
        if not cover:
            raise ValueError(f'Cover does not exist: {source_id} -> {target_id}')
        self._covers.pop(source_id)

    def edge_likes(self, *, source_id: NodeIdLike | None = None, target_id: NodeIdLike | None = None) -> list[EdgeLike]:
        return cast('List[KCFG.EdgeLike]', self.edges(source_id=source_id, target_id=target_id)) + cast(
            'List[KCFG.EdgeLike]', self.covers(source_id=source_id, target_id=target_id)
        )

    def add_vacuous(self, node_id: NodeIdLike) -> None:
        self.add_attr(node_id, KCFGNodeAttr.VACUOUS)

    def remove_vacuous(self, node_id: NodeIdLike) -> None:
        self.remove_attr(node_id, KCFGNodeAttr.VACUOUS)

    def discard_vacuous(self, node_id: NodeIdLike) -> None:
        self.discard_attr(node_id, KCFGNodeAttr.VACUOUS)

    def add_stuck(self, node_id: NodeIdLike) -> None:
        self.add_attr(node_id, KCFGNodeAttr.STUCK)

    def remove_stuck(self, node_id: NodeIdLike) -> None:
        self.remove_attr(node_id, KCFGNodeAttr.STUCK)

    def discard_stuck(self, node_id: NodeIdLike) -> None:
        self.discard_attr(node_id, KCFGNodeAttr.STUCK)

    def splits(self, *, source_id: NodeIdLike | None = None, target_id: NodeIdLike | None = None) -> list[Split]:
        source_id = self._resolve(source_id) if source_id is not None else None
        target_id = self._resolve(target_id) if target_id is not None else None
        return [
            s
            for s in self._splits.values()
            if (source_id is None or source_id == s.source.id) and (target_id is None or target_id in s.target_ids)
        ]

    def contains_split(self, split: Split) -> bool:
        return split in self._splits.values()

    def create_split(self, source_id: NodeIdLike, splits: Iterable[tuple[NodeIdLike, CSubst]]) -> KCFG.Split:
        source_id = self._resolve(source_id)
        split = KCFG.Split(self.node(source_id), tuple((self.node(nid), csubst) for nid, csubst in list(splits)))
        self.add_successor(split)
        return split

    def ndbranches(self, *, source_id: NodeIdLike | None = None, target_id: NodeIdLike | None = None) -> list[NDBranch]:
        source_id = self._resolve(source_id) if source_id is not None else None
        target_id = self._resolve(target_id) if target_id is not None else None
        return [
            b
            for b in self._ndbranches.values()
            if (source_id is None or source_id == b.source.id) and (target_id is None or target_id in b.target_ids)
        ]

    def contains_ndbranch(self, ndbranch: NDBranch) -> bool:
        return ndbranch in self._ndbranches

    def create_ndbranch(
        self, source_id: NodeIdLike, ndbranches: Iterable[NodeIdLike], rules: Iterable[str] = ()
    ) -> KCFG.NDBranch:
        source_id = self._resolve(source_id)
        ndbranch = KCFG.NDBranch(self.node(source_id), tuple(self.node(nid) for nid in list(ndbranches)), tuple(rules))
        self.add_successor(ndbranch)
        return ndbranch

    def split_on_constraints(self, source_id: NodeIdLike, constraints: Iterable[KInner]) -> list[int]:
        source = self.node(source_id)
        branch_node_ids = [self.create_node(source.cterm.add_constraint(c)).id for c in constraints]
        csubsts = [not_none(source.cterm.match_with_constraint(self.node(id).cterm)) for id in branch_node_ids]
        csubsts = [
            reduce(CSubst.add_constraint, flatten_label('#And', constraint), csubst)
            for (csubst, constraint) in zip(csubsts, constraints, strict=True)
        ]
        self.create_split(source.id, zip(branch_node_ids, csubsts, strict=True))
        return branch_node_ids

    def lift_edge(self, b_id: NodeIdLike) -> None:
        """Lift an edge up another edge directly preceding it.

        Input:
            -   b_id: the identifier of the central node `B` of a sequence of edges `A --> B --> C`.

        Effect: `A --M steps--> B --N steps--> C` becomes `A --(M + N) steps--> C`. Node `B` is removed.

        Output: None

        Raises: An `AssertionError` if the edges in question are not in place.
        """

        # Obtain edges `A -> B`, `B -> C`
        a_to_b = single(self.edges(target_id=b_id))
        b_to_c = single(self.edges(source_id=b_id))
        # Remove the node `B`, effectively removing the entire initial structure
        self.remove_node(b_id)
        # Create edge `A -> C`
        self.create_edge(a_to_b.source.id, b_to_c.target.id, a_to_b.depth + b_to_c.depth, a_to_b.rules + b_to_c.rules)

    def lift_edges(self) -> bool:
        """Perform all possible edge lifts across the KCFG.

        Given the KCFG design, it is not possible for one edge lift to either disallow another or
        allow another that was not previously possible. Therefore, this function is guaranteed to
        lift all possible edges without having to loop.

        Input: None

        Effect: The KCFG is transformed to an equivalent in which no further edge lifts are possible.

        Output:
            -   bool: An indicator of whether or not at least one edge lift was performed.
        """

        edges_to_lift = sorted(
            [
                node.id
                for node in self.nodes
                if len(self.edges(source_id=node.id)) > 0 and len(self.edges(target_id=node.id)) > 0
            ]
        )
        for node_id in edges_to_lift:
            self.lift_edge(node_id)
        return len(edges_to_lift) > 0

    def lift_split_edge(self, b_id: NodeIdLike) -> None:
        """Lift a split up an edge directly preceding it.

        Input:
            -   b_id: the identifier of the central node `B` of the structure `A --> B --> [C_1, ..., C_N]`.

        Effect:
            `A --M steps--> B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]` becomes
            `A --[cond_1, ..., cond_N]--> [A #And cond_1 --M steps--> C_1, ..., A #And cond_N --M steps--> C_N]`.
            Node `B` is removed.

        Output: None

        Raises:
            -   `AssertionError`, if the structure in question is not in place.
            -   `AssertionError`, if any of the `cond_i` contain variables not present in `A`.
        """

        # Obtain edge `A -> B`, split `[cond_I, C_I | I = 1..N ]`
        a_to_b = single(self.edges(target_id=b_id))
        a = a_to_b.source
        split_from_b = single(self.splits(source_id=b_id))
        ci, csubsts = list(split_from_b.splits.keys()), list(split_from_b.splits.values())
        # Ensure split can be lifted soundly (i.e., that it does not introduce fresh variables)
        assert (
            len(split_from_b.source_vars.difference(a.free_vars)) == 0
            and len(split_from_b.target_vars.difference(split_from_b.source_vars)) == 0
        )
        # Create CTerms and CSubsts corresponding to the new targets of the split
        new_cterms_with_constraints = [
            (CTerm(a.cterm.config, a.cterm.constraints + csubst.constraints), csubst.constraint) for csubst in csubsts
        ]
        # Generate substitutions for new targets, which all exist by construction
        new_csubsts = [
            not_none(a.cterm.match_with_constraint(cterm)).add_constraint(constraint)
            for (cterm, constraint) in new_cterms_with_constraints
        ]
        # Remove the node `B`, effectively removing the entire initial structure
        self.remove_node(b_id)
        # Create the nodes `[ A #And cond_I | I = 1..N ]`.
        ai: list[NodeIdLike] = [self.create_node(cterm).id for (cterm, _) in new_cterms_with_constraints]
        # Create the edges `[A #And cond_1 --M steps--> C_I | I = 1..N ]`
        for i in range(len(ai)):
            self.create_edge(ai[i], ci[i], a_to_b.depth, a_to_b.rules)
        # Create the split `A --[cond_1, ..., cond_N]--> [A #And cond_1, ..., A #And cond_N]
        self.create_split(a.id, zip(ai, new_csubsts, strict=True))

    def lift_split_split(self, b_id: NodeIdLike) -> None:
        """Lift a split up a split directly preceding it, joining them into a single split.

        Input:
            -   b_id: the identifier of the node `B` of the structure
                `A --[..., cond_B, ...]--> [..., B, ...]` with `B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]`

        Effect:
            `A --[..., cond_B, ...]--> [..., B, ...]` with `B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]` becomes
            `A --[..., cond_B #And cond_1, ..., cond_B #And cond_N, ...]--> [..., C_1, ..., C_N, ...]`.
            Node `B` is removed.

        Output: None

        Raises:
            -   `AssertionError`, if the structure in question is not in place.
        """
        # Obtain splits `A --[..., cond_B, ...]--> [..., B, ...]` and
        # `B --[cond_1, ..., cond_N]--> [C_1, ..., C_N]-> [C_1, ..., C_N]`
        split_from_a, split_from_b = single(self.splits(target_id=b_id)), single(self.splits(source_id=b_id))
        splits_from_a, splits_from_b = split_from_a.splits, split_from_b.splits
        a = split_from_a.source
        ci = list(splits_from_b.keys())
        # Ensure split can be lifted soundly (i.e., that it does not introduce fresh variables)
        assert (
            len(split_from_b.source_vars.difference(a.free_vars)) == 0
            and len(split_from_b.target_vars.difference(split_from_b.source_vars)) == 0
        )
        # Get the substitution for `B`, at the same time removing 'B' from the targets of `A`.
        csubst_b = splits_from_a.pop(self._resolve(b_id))
        # Generate substitutions for additional targets `C_I`, which all exist by construction;
        # the constraints are cumulative, resulting in `cond_B #And cond_I`
        additional_csubsts = [
            not_none(a.cterm.match_with_constraint(self.node(ci).cterm))
            .add_constraint(csubst_b.constraint)
            .add_constraint(csubst.constraint)
            for ci, csubst in splits_from_b.items()
        ]
        # Create the targets of the new split
        ci = list(splits_from_b.keys())
        new_splits = zip(
            list(splits_from_a.keys()) + ci, list(splits_from_a.values()) + additional_csubsts, strict=True
        )
        # Remove the node `B`, thereby removing the two splits as well
        self.remove_node(b_id)
        # Create the new split `A --[..., cond_B #And cond_1, ..., cond_B #And cond_N, ...]--> [..., C_1, ..., C_N, ...]`
        self.create_split(a.id, new_splits)

    def lift_splits(self) -> bool:
        """Perform all possible split liftings.

        Input: None

        Effect: The KCFG is transformed to an equivalent in which no further split lifts are possible.

        Output:
            -   bool: An indicator of whether or not at least one split lift was performed.
        """

        def _lift_split(finder: Callable, lifter: Callable) -> bool:
            result = False
            while True:
                splits_to_lift = sorted(
                    [
                        node.id
                        for node in self.nodes
                        if (splits := self.splits(source_id=node.id)) != []
                        and (sources := finder(target_id=node.id)) != []
                        and (source := single(sources).source)
                        and (split := single(splits))
                        and len(split.source_vars.difference(source.free_vars)) == 0
                        and len(split.target_vars.difference(split.source_vars)) == 0
                    ]
                )
                for id in splits_to_lift:
                    lifter(id)
                    result = True
                if len(splits_to_lift) == 0:
                    break
            return result

        def _fold_lift(result: bool, finder_lifter: tuple[Callable, Callable]) -> bool:
            return _lift_split(finder_lifter[0], finder_lifter[1]) or result

        return reduce(_fold_lift, [(self.edges, self.lift_split_edge), (self.splits, self.lift_split_split)], False)

    def minimize(self) -> None:
        """Minimize KCFG by repeatedly performing the lifting transformations.

        The loop is designed so that each transformation is performed once in each iteration.

        Input: None

        Effect: The KCFG is transformed to an equivalent in which no further lifting transformations are possible.

        Output: None
        """

        repeat = True
        while repeat:
            repeat = self.lift_edges()
            repeat = self.lift_splits() or repeat

    def add_alias(self, alias: str, node_id: NodeIdLike) -> None:
        if '@' in alias:
            raise ValueError('Alias may not contain "@"')
        if alias in self._aliases:
            raise ValueError(f'Duplicate alias: {alias}')
        node_id = self._resolve(node_id)
        self._aliases[alias] = node_id

    def remove_alias(self, alias: str) -> None:
        if alias not in self._aliases:
            raise ValueError(f'Alias does not exist: {alias}')
        self._aliases.pop(alias)

    def is_root(self, node_id: NodeIdLike) -> bool:
        node_id = self._resolve(node_id)
        return len(self.predecessors(node_id)) == 0

    def is_vacuous(self, node_id: NodeIdLike) -> bool:
        return KCFGNodeAttr.VACUOUS in self.node(node_id).attrs

    def is_stuck(self, node_id: NodeIdLike) -> bool:
        return KCFGNodeAttr.STUCK in self.node(node_id).attrs

    def is_split(self, node_id: NodeIdLike) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._splits

    def is_ndbranch(self, node_id: NodeIdLike) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._ndbranches

    def is_leaf(self, node_id: NodeIdLike) -> bool:
        return len(self.successors(node_id)) == 0

    def is_covered(self, node_id: NodeIdLike) -> bool:
        node_id = self._resolve(node_id)
        return node_id in self._covers

    def prune(self, node_id: NodeIdLike, keep_nodes: Iterable[NodeIdLike] = ()) -> list[int]:
        nodes = self.reachable_nodes(node_id)
        keep_nodes = [self._resolve(nid) for nid in keep_nodes]
        pruned_nodes: list[int] = []
        for node in nodes:
            if node.id not in keep_nodes:
                self.remove_node(node.id)
                pruned_nodes.append(node.id)
        return pruned_nodes

    def shortest_path_between(
        self, source_node_id: NodeIdLike, target_node_id: NodeIdLike
    ) -> tuple[Successor, ...] | None:
        paths = self.paths_between(source_node_id, target_node_id)
        if len(paths) == 0:
            return None
        return sorted(paths, key=(lambda path: KCFG.path_length(path)))[0]

    def shortest_distance_between(self, node_1_id: NodeIdLike, node_2_id: NodeIdLike) -> int | None:
        path_1 = self.shortest_path_between(node_1_id, node_2_id)
        path_2 = self.shortest_path_between(node_2_id, node_1_id)
        distance: int | None = None
        if path_1 is not None:
            distance = KCFG.path_length(path_1)
        if path_2 is not None:
            distance_2 = KCFG.path_length(path_2)
            if distance is None or distance_2 < distance:
                distance = distance_2
        return distance

    def zero_depth_between(self, node_1_id: NodeIdLike, node_2_id: NodeIdLike) -> bool:
        shortest_distance = self.shortest_distance_between(node_1_id, node_2_id)
        return shortest_distance is not None and shortest_distance == 0

    def paths_between(self, source_id: NodeIdLike, target_id: NodeIdLike) -> list[tuple[Successor, ...]]:
        source_id = self._resolve(source_id)
        target_id = self._resolve(target_id)

        if source_id == target_id:
            return [()]

        source_successors = list(self.successors(source_id))
        assert len(source_successors) <= 1
        if len(source_successors) == 0:
            return []

        paths: list[tuple[KCFG.Successor, ...]] = []
        worklist: list[list[KCFG.Successor]] = [[source_successors[0]]]

        def _in_path(_nid: int, _path: list[KCFG.Successor]) -> bool:
            for succ in _path:
                if _nid == succ.source.id:
                    return True
            if len(_path) > 0:
                if isinstance(_path[-1], KCFG.EdgeLike) and _path[-1].target.id == _nid:
                    return True
                elif isinstance(_path[-1], KCFG.MultiEdge) and _nid in _path[-1].target_ids:
                    return True
            return False

        while worklist:
            curr_path = worklist.pop()
            curr_successor = curr_path[-1]
            successors: list[KCFG.Successor] = []

            if isinstance(curr_successor, KCFG.EdgeLike):
                if curr_successor.target.id == target_id:
                    paths.append(tuple(curr_path))
                    continue
                else:
                    successors = list(self.successors(curr_successor.target.id))

            elif isinstance(curr_successor, KCFG.MultiEdge):
                if len(list(curr_successor.targets)) == 1:
                    target = list(curr_successor.targets)[0]
                    if target.id == target_id:
                        paths.append(tuple(curr_path))
                        continue
                    else:
                        successors = list(self.successors(target.id))
                if len(list(curr_successor.targets)) > 1:
                    curr_path = curr_path[0:-1]
                    successors = [curr_successor.with_single_target(target) for target in curr_successor.targets]

            for successor in successors:
                if isinstance(successor, KCFG.EdgeLike) and not _in_path(successor.target.id, curr_path):
                    worklist.append(curr_path + [successor])
                elif isinstance(successor, KCFG.MultiEdge):
                    if len(list(successor.targets)) == 1:
                        target = list(successor.targets)[0]
                        if not _in_path(target.id, curr_path):
                            worklist.append(curr_path + [successor])
                    elif len(list(successor.targets)) > 1:
                        worklist.append(curr_path + [successor])

        return paths

    def reachable_nodes(self, source_id: NodeIdLike, *, reverse: bool = False) -> set[KCFG.Node]:
        visited: set[KCFG.Node] = set()
        worklist: list[KCFG.Node] = [self.node(source_id)]

        while worklist:
            node = worklist.pop()

            if node in visited:
                continue

            visited.add(node)

            if not reverse:
                worklist.extend(target for succ in self.successors(source_id=node.id) for target in succ.targets)
            else:
                worklist.extend(succ.source for succ in self.predecessors(target_id=node.id))

        return visited

    def write_cfg_data(self) -> None:
        assert self._kcfg_store is not None
        self._kcfg_store.write_cfg_data(
            self.to_dict(), deleted_nodes=self._deleted_nodes, created_nodes=self._created_nodes
        )
        self._deleted_nodes.clear()
        self._created_nodes.clear()

    @staticmethod
    def read_cfg_data(cfg_dir: Path) -> KCFG:
        store = KCFGStore(cfg_dir)
        cfg = KCFG.from_dict(store.read_cfg_data())
        cfg._kcfg_store = store
        return cfg

    @staticmethod
    def read_node_data(cfg_dir: Path, node_id: int) -> KCFG.Node:
        store = KCFGStore(cfg_dir)
        return KCFG.Node.from_dict(store.read_node_data(node_id))


class KCFGExtendResult(ABC): ...


@final
@dataclass(frozen=True)
class Vacuous(KCFGExtendResult): ...


@final
@dataclass(frozen=True)
class Stuck(KCFGExtendResult): ...


@final
@dataclass(frozen=True)
class Abstract(KCFGExtendResult):
    cterm: CTerm


@final
@dataclass(frozen=True)
class Step(KCFGExtendResult):
    cterm: CTerm
    depth: int
    logs: tuple[LogEntry, ...]
    rule_labels: list[str]
    cut: bool = field(default=False)


@final
@dataclass(frozen=True)
class Branch(KCFGExtendResult):
    constraints: tuple[KInner, ...]
    heuristic: bool

    def __init__(self, constraints: Iterable[KInner], *, heuristic: bool = False):
        object.__setattr__(self, 'constraints', tuple(constraints))
        object.__setattr__(self, 'heuristic', heuristic)


@final
@dataclass(frozen=True)
class NDBranch(KCFGExtendResult):
    cterms: tuple[CTerm, ...]
    logs: tuple[LogEntry, ...]
    rule_labels: tuple[str, ...]

    def __init__(self, cterms: Iterable[CTerm], logs: Iterable[LogEntry,], rule_labels: Iterable[str]):
        object.__setattr__(self, 'cterms', tuple(cterms))
        object.__setattr__(self, 'logs', tuple(logs))
        object.__setattr__(self, 'rule_labels', tuple(rule_labels))
