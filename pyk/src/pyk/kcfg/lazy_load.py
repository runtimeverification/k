"""Load a KCFG from disk with lazy node CTerms and cover CSubsts.

Nodes are represented as LazyNode stubs that load CTerms on demand.
Cover CSubsts are wrapped as LazyCSubst to defer parsing.
Edges, splits, and ndbranches are constructed with the actual KCFG types
using stub nodes.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING

from .kcfg import KCFG, KCFGNodeAttr
from .lazy import LazyCSubst, LazyNode

if TYPE_CHECKING:
    pass


def read_cfg_lazy(cfg_dir: Path) -> KCFG:
    """Read a KCFG from disk without loading node CTerms or cover CSubsts eagerly.

    Returns a real KCFG object populated with LazyNode stubs and LazyCSubst wrappers.
    The existing pretty_segments traversal works unchanged on this KCFG.
    """
    from ..cterm import CSubst

    kcfg_json_path = cfg_dir / 'kcfg.json'
    node_dir = cfg_dir / 'nodes'

    dct = json.loads(kcfg_json_path.read_text())

    node_ids = dct.get('nodes') or []
    vacuous_ids = set(dct.get('vacuous') or [])
    stuck_ids = set(dct.get('stuck') or [])

    # Build lazy nodes
    nodes: dict[int, LazyNode] = {}
    for nid in node_ids:
        attrs = frozenset()
        if nid in vacuous_ids:
            attrs = frozenset([KCFGNodeAttr.VACUOUS])
        if nid in stuck_ids:
            attrs = frozenset(attrs | {KCFGNodeAttr.STUCK})
        nodes[nid] = LazyNode(nid, attrs, node_dir / f'{nid}.json')

    # Build KCFG without optimize_memory (stubs aren't real KInner terms)
    cfg = KCFG(optimize_memory=False)

    # Add nodes — KCFG.add_node expects KCFG.Node, but we pass LazyNode (duck typing)
    for node in nodes.values():
        cfg._nodes[node.id] = node  # type: ignore[assignment]
        cfg._node_id = max(cfg._node_id, node.id + 1)

    cfg._node_id = dct.get('next', cfg._node_id)

    # Edges — lightweight (just depth + rules)
    for edge_dict in dct.get('edges') or []:
        src = nodes[edge_dict['source']]
        tgt = nodes[edge_dict['target']]
        edge = KCFG.Edge(src, tgt, edge_dict['depth'], tuple(edge_dict.get('rules') or []))  # type: ignore[arg-type]
        cfg._edges[src.id] = edge

    # Merged edges
    for me_dict in dct.get('merged_edges') or []:
        src = nodes[me_dict['source']]
        tgt = nodes[me_dict['target']]
        sub_edges = tuple(
            KCFG.Edge(nodes[e['source']], nodes[e['target']], e['depth'], tuple(e.get('rules') or []))  # type: ignore[arg-type]
            for e in me_dict['edges']
        )
        merged = KCFG.MergedEdge(src, tgt, sub_edges)  # type: ignore[arg-type]
        cfg._merged_edges[src.id] = merged

    # Splits — CSubst per target loaded eagerly (32 MB total, acceptable)
    for split_dict in dct.get('splits') or []:
        src = nodes[split_dict['source']]
        targets = []
        for t in split_dict['targets']:
            tgt_node = nodes[t['target']]
            csubst = CSubst.from_dict(t['csubst'])
            targets.append((tgt_node, csubst))
        split = KCFG.Split(src, tuple(targets))  # type: ignore[arg-type]
        cfg._splits[src.id] = split

    # Covers — CSubst wrapped as LazyCSubst (792 MB deferred)
    for cover_dict in dct.get('covers') or []:
        src = nodes[cover_dict['source']]
        tgt = nodes[cover_dict['target']]
        lazy_csubst = LazyCSubst(cover_dict['csubst'])
        cover = KCFG.Cover(src, tgt, lazy_csubst)  # type: ignore[arg-type]
        cfg._covers[src.id] = cover

    # NDBranches
    for nb_dict in dct.get('ndbranches') or []:
        src = nodes[nb_dict['source']]
        tgt_nodes = tuple(nodes[tid] for tid in nb_dict['targets'])
        nb = KCFG.NDBranch(src, tgt_nodes, tuple(nb_dict.get('rules') or []))  # type: ignore[arg-type]
        cfg._ndbranches[src.id] = nb

    # Aliases
    for alias, node_id in dct.get('aliases', {}).items():
        cfg._aliases[alias] = node_id

    return cfg
