from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..kcfg.show import KCFGShow, NodePrinter
from ..utils import ensure_dir_path

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Final

    from graphviz import Digraph

    from ..kcfg import KCFG
    from ..kcfg.kcfg import NodeIdLike
    from ..ktool.kprint import KPrint
    from .reachability import APRProof

_LOGGER: Final = logging.getLogger(__name__)


class APRProofNodePrinter(NodePrinter):
    proof: APRProof

    def __init__(self, proof: APRProof, kprint: KPrint, full_printer: bool = False, minimize: bool = False):
        super().__init__(kprint, full_printer=full_printer, minimize=minimize)
        self.proof = proof

    def node_attrs(self, kcfg: KCFG, node: KCFG.Node) -> list[str]:
        attrs = super().node_attrs(kcfg, node)
        if self.proof.is_init(node.id):
            attrs.append('init')
        if self.proof.is_target(node.id):
            attrs.append('target')
        if self.proof.is_pending(node.id):
            attrs.append('pending')
        if self.proof.is_refuted(node.id):
            attrs.append('refuted')
        if self.proof.is_terminal(node.id):
            attrs.append('terminal')
            if 'stuck' in attrs:
                attrs.remove('stuck')
        if self.proof.is_bounded(node.id):
            attrs.append('bounded')
            if 'stuck' in attrs:
                attrs.remove('stuck')
        return attrs


class APRProofShow:
    kcfg_show: KCFGShow

    def __init__(self, kprint: KPrint, node_printer: NodePrinter | None = None):
        self.kcfg_show = KCFGShow(kprint, node_printer=node_printer)

    def pretty_segments(self, proof: APRProof, minimize: bool = True) -> Iterable[tuple[str, Iterable[str]]]:
        ret_lines = list(self.kcfg_show.pretty_segments(proof.kcfg, minimize=minimize))
        if len(proof.pending) > 0:
            target_node_lines = ['', 'Target Node:']
            target_node_lines += self.kcfg_show.node_printer.print_node(proof.kcfg, proof.kcfg.node(proof.target))
            ret_lines.append((f'node_{proof.target}', target_node_lines))
        return KCFGShow.make_unique_segments(ret_lines)

    def pretty(self, proof: APRProof, minimize: bool = True) -> Iterable[str]:
        return (line for _, seg_lines in self.pretty_segments(proof, minimize=minimize) for line in seg_lines)

    def show(
        self,
        proof: APRProof,
        nodes: Iterable[NodeIdLike] = (),
        node_deltas: Iterable[tuple[NodeIdLike, NodeIdLike]] = (),
        to_module: bool = False,
        minimize: bool = True,
        sort_collections: bool = False,
        omit_cells: Iterable[str] = (),
    ) -> list[str]:
        res_lines = self.kcfg_show.show(
            proof.kcfg,
            nodes=nodes,
            node_deltas=node_deltas,
            to_module=to_module,
            minimize=minimize,
            sort_collections=sort_collections,
            omit_cells=omit_cells,
            module_name=f'SUMMARY-{proof.id.upper().replace("_", "-")}',
        )
        return res_lines

    def dot(self, proof: APRProof) -> Digraph:
        graph = self.kcfg_show.dot(proof.kcfg)
        attrs = {'class': 'target', 'style': 'solid'}
        for node in proof.pending:
            graph.edge(tail_name=node.id, head_name=proof.target, label=' ???', **attrs)
        for node in proof.kcfg.stuck:
            graph.edge(tail_name=node.id, head_name=proof.target, label=' false', **attrs)
        return graph

    def dump(self, proof: APRProof, dump_dir: Path, dot: bool = False) -> None:
        ensure_dir_path(dump_dir)

        proof_file = dump_dir / f'{proof.id}.json'
        proof_file.write_text(proof.json)
        _LOGGER.info(f'Wrote CFG file {proof.id}: {proof_file}')

        if dot:
            proof_dot = self.dot(proof)
            dot_file = dump_dir / f'{proof.id}.dot'
            dot_file.write_text(proof_dot.source)
            _LOGGER.info(f'Wrote DOT file {proof.id}: {dot_file}')

        self.kcfg_show.dump(f'{proof.id}_cfg', proof.kcfg, dump_dir, dot=False)
