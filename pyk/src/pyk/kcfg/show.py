from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..cli_utils import ensure_dir_path
from ..cterm import CTerm, build_claim, build_rule
from ..kast.inner import KApply, KRewrite, top_down
from ..kast.manip import flatten_label, minimize_term, push_down_rewrites
from ..kast.outer import KFlatModule
from ..prelude.k import DOTS
from ..prelude.ml import mlAnd
from .kcfg import KCFG

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable
    from pathlib import Path
    from typing import Final

    from ..kast import KInner
    from ..kast.outer import KRuleLike
    from ..ktool.kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


class KCFGShow:
    kprint: KPrint

    def __init__(
        self,
        kprint: KPrint,
    ):
        self.kprint = kprint

    def show(
        self,
        cfgid: str,
        cfg: KCFG,
        nodes: Iterable[str] = (),
        node_deltas: Iterable[tuple[str, str]] = (),
        to_module: bool = False,
        minimize: bool = True,
        node_printer: Callable[[CTerm], Iterable[str]] | None = None,
        omit_node_hash: bool = False,
        omit_cells: Iterable[str] = (),
    ) -> list[str]:
        res_lines: list[str] = []
        res_lines += cfg.pretty(
            self.kprint, minimize=minimize, node_printer=node_printer, omit_node_hash=omit_node_hash
        )

        def hide_cells(term: KInner) -> KInner:
            def _hide_cells(_k: KInner) -> KInner:
                if type(_k) == KApply and _k.label.name in omit_cells:
                    return DOTS
                return _k

            if omit_cells:
                return top_down(_hide_cells, term)
            return term

        nodes_printed = False

        for node_id in nodes:
            nodes_printed = True
            kast = cfg.node(node_id).cterm.kast
            kast = hide_cells(kast)
            if minimize:
                kast = minimize_term(kast)
            res_lines.append('')
            res_lines.append('')
            if omit_node_hash:
                res_lines.append('Node OMITTED HASH:')
            else:
                res_lines.append(f'Node {node_id}:')
            res_lines.append('')
            res_lines.append(self.kprint.pretty_print(kast))
            res_lines.append('')

        for node_id_1, node_id_2 in node_deltas:
            nodes_printed = True
            config_1 = cfg.node(node_id_1).cterm.config
            config_2 = cfg.node(node_id_2).cterm.config
            config_1 = hide_cells(config_1)
            config_2 = hide_cells(config_2)
            config_delta = push_down_rewrites(KRewrite(config_1, config_2))
            if minimize:
                config_delta = minimize_term(config_delta)
            res_lines.append('')
            res_lines.append('')
            res_lines.append(f'State Delta {node_id_1} => {node_id_2}:')
            res_lines.append('')
            res_lines.append(self.kprint.pretty_print(config_delta))
            res_lines.append('')

        if not (nodes_printed):
            res_lines.append('')
        res_lines.append('')
        res_lines.append('')

        if to_module:

            def to_rule(edge: KCFG.Edge, *, claim: bool = False) -> KRuleLike:
                sentence_id = f'BASIC-BLOCK-{edge.source.id}-TO-{edge.target.id}'
                init_cterm = CTerm(hide_cells(edge.source.cterm.config), ())
                for c in edge.source.cterm.constraints:
                    assert type(c) is KApply
                    if c.label.name == '#Ceil':
                        _LOGGER.warning(f'Ignoring Ceil condition: {c}')
                    else:
                        init_cterm.add_constraint(c)
                target_cterm = CTerm(hide_cells(edge.target.cterm.config), ())
                for c in edge.source.cterm.constraints:
                    assert type(c) is KApply
                    if c.label.name == '#Ceil':
                        _LOGGER.warning(f'Ignoring Ceil condition: {c}')
                    else:
                        target_cterm.add_constraint(c)
                rule: KRuleLike
                if claim:
                    rule, _ = build_claim(sentence_id, init_cterm, target_cterm)
                else:
                    rule, _ = build_rule(sentence_id, init_cterm, target_cterm, priority=35)
                return rule

            rules = [to_rule(e) for e in cfg.edges() if e.depth > 0]
            claims = [to_rule(KCFG.Edge(nd, cfg.get_unique_target(), -1), claim=True) for nd in cfg.frontier]
            cfg_module_name = cfgid.upper().replace('.', '-').replace('_', '-')
            new_module = KFlatModule(f'SUMMARY-{cfg_module_name}', rules + claims)
            res_lines.append(self.kprint.pretty_print(new_module))
            res_lines.append('')

        return res_lines

    def dump(
        self,
        cfgid: str,
        cfg: KCFG,
        dump_dir: Path,
        dot: bool = False,
        node_printer: Callable[[CTerm], Iterable[str]] | None = None,
    ) -> None:
        ensure_dir_path(dump_dir)

        cfg_file = dump_dir / f'{cfgid}.json'
        cfg_file.write_text(cfg.to_json())
        _LOGGER.info(f'Wrote CFG file {cfgid}: {cfg_file}')

        if dot:
            cfg_dot = cfg.to_dot(self.kprint, node_printer=node_printer)
            dot_file = dump_dir / f'{cfgid}.dot'
            dot_file.write_text(cfg_dot)
            _LOGGER.info(f'Wrote DOT file {cfgid}: {dot_file}')

        nodes_dir = dump_dir / 'nodes'
        for node in cfg.nodes:
            node_file = nodes_dir / f'config_{node.id}.txt'
            node_minimized_file = nodes_dir / f'config_minimized_{node.id}.txt'
            node_constraint_file = nodes_dir / f'constraint_{node.id}.txt'

            config = node.cterm.config
            if not node_file.exists():
                node_file.write_text(self.kprint.pretty_print(config))
                _LOGGER.info(f'Wrote node file {cfgid}: {node_file}')
            config = minimize_term(config)
            if not node_minimized_file.exists():
                node_minimized_file.write_text(self.kprint.pretty_print(config))
                _LOGGER.info(f'Wrote node file {cfgid}: {node_minimized_file}')
            if not node_constraint_file.exists():
                constraint = mlAnd(node.cterm.constraints)
                node_constraint_file.write_text(self.kprint.pretty_print(constraint))
                _LOGGER.info(f'Wrote node file {cfgid}: {node_constraint_file}')

        edges_dir = dump_dir / 'edges'
        for edge in cfg.edges():
            edge_file = edges_dir / f'config_{edge.source.id}_{edge.target.id}.txt'
            edge_minimized_file = edges_dir / f'config_minimized_{edge.source.id}_{edge.target.id}.txt'

            config = push_down_rewrites(KRewrite(edge.source.cterm.config, edge.target.cterm.config))
            if not edge_file.exists():
                edge_file.write_text(self.kprint.pretty_print(config))
                _LOGGER.info(f'Wrote edge file {cfgid}: {edge_file}')
            config = minimize_term(config)
            if not edge_minimized_file.exists():
                edge_minimized_file.write_text(self.kprint.pretty_print(config))
                _LOGGER.info(f'Wrote edge file {cfgid}: {edge_minimized_file}')

        covers_dir = dump_dir / 'covers'
        for cover in cfg.covers():
            cover_file = covers_dir / f'config_{cover.source.id}_{cover.target.id}.txt'
            cover_constraint_file = covers_dir / f'constraint_{cover.source.id}_{cover.target.id}.txt'

            subst_equalities = flatten_label('#And', cover.csubst.subst.ml_pred)

            if not cover_file.exists():
                cover_file.write_text('\n'.join(self.kprint.pretty_print(se) for se in subst_equalities))
                _LOGGER.info(f'Wrote cover file {cfgid}: {cover_file}')
            if not cover_constraint_file.exists():
                cover_constraint_file.write_text(self.kprint.pretty_print(cover.csubst.constraint))
                _LOGGER.info(f'Wrote cover file {cfgid}: {cover_constraint_file}')
