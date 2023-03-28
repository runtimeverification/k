from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING, ContextManager

from ..cterm import CSubst, CTerm
from ..kast.inner import KApply, KLabel, KVariable, Subst
from ..kast.manip import flatten_label, free_vars
from ..kore.rpc import KoreClient, KoreServer
from ..prelude.k import GENERATED_TOP_CELL
from ..prelude.ml import is_bottom, is_top, mlAnd, mlEquals, mlTop
from ..utils import hash_str, shorten_hashes, single
from .kcfg import KCFG

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Any, Callable, Dict, Final, Iterable, List, Optional, Tuple, Union

    from ..cli_utils import BugReport
    from ..kast import KInner
    from ..ktool.kprint import KPrint


_LOGGER: Final = logging.getLogger(__name__)


class KCFGExplore(ContextManager['KCFGExplore']):
    kprint: KPrint
    _port: Optional[int]
    _kore_rpc_command: Union[str, Iterable[str]]
    _smt_timeout: Optional[int]
    _smt_retry_limit: Optional[int]
    _bug_report: Optional[BugReport]

    _kore_server: Optional[KoreServer]
    _kore_client: Optional[KoreClient]
    _rpc_closed: bool

    def __init__(
        self,
        kprint: KPrint,
        *,
        port: Optional[int] = None,
        kore_rpc_command: Union[str, Iterable[str]] = 'kore-rpc',
        smt_timeout: Optional[int] = None,
        smt_retry_limit: Optional[int] = None,
        bug_report: Optional[BugReport] = None,
    ):
        self.kprint = kprint
        self._port = port
        self._kore_rpc_command = kore_rpc_command
        self._smt_timeout = smt_timeout
        self._smt_retry_limit = smt_retry_limit
        self._bug_report = bug_report
        self._kore_server = None
        self._kore_client = None
        self._rpc_closed = False

    def __enter__(self) -> KCFGExplore:
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    @staticmethod
    def read_cfg(cfgid: str, kcfgs_dir: Path) -> Optional[KCFG]:
        cfg_path = kcfgs_dir / f'{hash_str(cfgid)}.json'
        if cfg_path.exists():
            cfg_dict = json.loads(cfg_path.read_text())
            _LOGGER.info(f'Reading KCFG from file {cfgid}: {cfg_path}')
            return KCFG.from_dict(cfg_dict)
        return None

    @staticmethod
    def write_cfg(cfgid: str, kcfgs_dir: Path, cfg: KCFG) -> None:
        cfg_dict = cfg.to_dict()
        cfg_dict['cfgid'] = cfgid
        cfg_path = kcfgs_dir / f'{hash_str(cfgid)}.json'
        cfg_path.write_text(json.dumps(cfg_dict))
        _LOGGER.info(f'Updated CFG file {cfgid}: {cfg_path}')

    @property
    def _kore_rpc(self) -> Tuple[KoreServer, KoreClient]:
        if self._rpc_closed:
            raise ValueError('RPC server already closed!')
        if not self._kore_server:
            self._kore_server = KoreServer(
                self.kprint.definition_dir,
                self.kprint.main_module,
                port=self._port,
                bug_report=self._bug_report,
                command=self._kore_rpc_command,
                smt_timeout=self._smt_timeout,
                smt_retry_limit=self._smt_retry_limit,
            )
        if not self._kore_client:
            self._kore_client = KoreClient('localhost', self._kore_server._port, bug_report=self._bug_report)
        return (self._kore_server, self._kore_client)

    def close(self) -> None:
        self._rpc_closed = True
        if self._kore_server is not None:
            self._kore_server.close()
            self._kore_server = None
        if self._kore_client is not None:
            self._kore_client.close()
            self._kore_client = None

    def cterm_execute(
        self,
        cterm: CTerm,
        depth: Optional[int] = None,
        cut_point_rules: Optional[Iterable[str]] = None,
        terminal_rules: Optional[Iterable[str]] = None,
    ) -> Tuple[int, CTerm, List[CTerm]]:
        _LOGGER.debug(f'Executing: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        er = kore_client.execute(kore, max_depth=depth, cut_point_rules=cut_point_rules, terminal_rules=terminal_rules)
        depth = er.depth
        next_state = CTerm(self.kprint.kore_to_kast(er.state.kore))
        _next_states = er.next_states if er.next_states is not None and len(er.next_states) > 1 else []
        # TODO: should not have to prune bottom branches, the backend should do this for us.
        next_states = []
        for ns in _next_states:
            _LOGGER.info(f'Checking for bottom branch: {ns}')
            _ns = self.cterm_simplify(CTerm(self.kprint.kore_to_kast(ns.kore)))
            if is_bottom(_ns):
                _LOGGER.warning(f'Found bottom branch: {ns}')
            else:
                next_states.append(CTerm(_ns))
        if len(next_states) == 1 and len(next_states) < len(_next_states):
            return depth + 1, next_states[0], []
        return depth, next_state, next_states

    def cterm_simplify(self, cterm: CTerm) -> KInner:
        _LOGGER.debug(f'Simplifying: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        kore_simplified = kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        return kast_simplified

    def cterm_implies(
        self, antecedent: CTerm, consequent: CTerm, bind_consequent_variables: bool = True
    ) -> Optional[CSubst]:
        _LOGGER.debug(f'Checking implication: {antecedent} #Implies {consequent}')
        _consequent = consequent.kast
        if bind_consequent_variables:
            _consequent = consequent.kast
            fv_antecedent = free_vars(antecedent.kast)
            unbound_consequent = [v for v in free_vars(_consequent) if v not in fv_antecedent]
            if len(unbound_consequent) > 0:
                _LOGGER.debug(f'Binding variables in consequent: {unbound_consequent}')
                for uc in unbound_consequent:
                    _consequent = KApply(KLabel('#Exists', [GENERATED_TOP_CELL]), [KVariable(uc), _consequent])
        antecedent_kore = self.kprint.kast_to_kore(antecedent.kast, GENERATED_TOP_CELL)
        consequent_kore = self.kprint.kast_to_kore(_consequent, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        result = kore_client.implies(antecedent_kore, consequent_kore)
        if not result.satisfiable:
            if result.substitution is not None:
                _LOGGER.debug(f'Received a non-empty substitution for unsatisfiable implication: {result.substitution}')
            if result.predicate is not None:
                _LOGGER.debug(f'Received a non-empty predicate for unsatisfiable implication: {result.predicate}')
            return None
        if result.substitution is None:
            raise ValueError('Received empty substutition for satisfiable implication.')
        if result.predicate is None:
            raise ValueError('Received empty predicate for satisfiable implication.')
        ml_subst = self.kprint.kore_to_kast(result.substitution)
        ml_pred = self.kprint.kore_to_kast(result.predicate) if result.predicate is not None else mlTop()
        ml_preds = flatten_label('#And', ml_pred)
        if is_top(ml_subst):
            return CSubst(subst=Subst({}), constraints=ml_preds)
        subst_pattern = mlEquals(KVariable('###VAR'), KVariable('###TERM'))
        _subst: Dict[str, KInner] = {}
        for subst_pred in flatten_label('#And', ml_subst):
            m = subst_pattern.match(subst_pred)
            if m is not None and type(m['###VAR']) is KVariable:
                _subst[m['###VAR'].name] = m['###TERM']
            else:
                raise AssertionError(f'Received a non-substitution from implies endpoint: {subst_pred}')
        return CSubst(subst=Subst(_subst), constraints=ml_preds)

    def cterm_assume_defined(self, cterm: CTerm) -> CTerm:
        _LOGGER.debug(f'Computing definedness condition for: {cterm}')
        kast = KApply(KLabel('#Ceil', [GENERATED_TOP_CELL, GENERATED_TOP_CELL]), [cterm.config])
        kore = self.kprint.kast_to_kore(kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        kore_simplified = kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        _LOGGER.debug(f'Definedness condition computed: {kast_simplified}')
        return cterm.add_constraint(kast_simplified)

    def remove_subgraph_from(self, cfgid: str, cfg: KCFG, node: str) -> KCFG:
        for _node in cfg.reachable_nodes(node, traverse_covers=True):
            if not cfg.is_target(_node.id):
                _LOGGER.info(f'Removing node: {shorten_hashes(_node.id)}')
                cfg.remove_node(_node.id)
        return cfg

    def simplify(self, cfgid: str, cfg: KCFG) -> KCFG:
        for node in cfg.nodes:
            _LOGGER.info(f'Simplifying node {cfgid}: {shorten_hashes(node.id)}')
            new_term = self.cterm_simplify(node.cterm)
            if is_top(new_term):
                raise ValueError(f'Node simplified to #Top {cfgid}: {shorten_hashes(node.id)}')
            if is_bottom(new_term):
                raise ValueError(f'Node simplified to #Bottom {cfgid}: {shorten_hashes(node.id)}')
            if new_term != node.cterm.kast:
                cfg.replace_node(node.id, CTerm(new_term))
        return cfg

    def step(self, cfgid: str, cfg: KCFG, node_id: str, depth: int = 1) -> Tuple[KCFG, str]:
        if depth <= 0:
            raise ValueError(f'Expected positive depth, got: {depth}')
        node = cfg.node(node_id)
        successors = list(cfg.successors(node.id))
        if len(successors) != 0 and type(successors[0]) is KCFG.Split:
            raise ValueError(f'Cannot take step from split node {cfgid}: {shorten_hashes(node.id)}')
        _LOGGER.info(f'Taking {depth} steps from node {cfgid}: {shorten_hashes(node.id)}')
        actual_depth, cterm, next_cterms = self.cterm_execute(node.cterm, depth=depth)
        if actual_depth != depth:
            raise ValueError(f'Unable to take {depth} steps from node, got {actual_depth} steps {cfgid}: {node.id}')
        if len(next_cterms) > 0:
            raise ValueError(f'Found branch within {depth} steps {cfgid}: {node.id}')
        new_node = cfg.get_or_create_node(cterm)
        _LOGGER.info(f'Found new node at depth {depth} {cfgid}: {shorten_hashes((node.id, new_node.id))}')
        out_edges = cfg.edges(source_id=node.id)
        if len(out_edges) == 0:
            cfg.create_edge(node.id, new_node.id, depth=depth)
        else:
            edge = out_edges[0]
            if depth > edge.depth:
                raise ValueError(
                    f'Step depth {depth} greater than original edge depth {edge.depth} {cfgid}: {shorten_hashes((edge.source.id, edge.target.id))}'
                )
            cfg.remove_edge(edge.source.id, edge.target.id)
            cfg.create_edge(edge.source.id, new_node.id, depth=depth)
            cfg.create_edge(new_node.id, edge.target.id, depth=(edge.depth - depth))
        return (cfg, new_node.id)

    def section_edge(
        self, cfgid: str, cfg: KCFG, source_id: str, target_id: str, sections: int = 2
    ) -> Tuple[KCFG, Tuple[str, ...]]:
        if sections <= 1:
            raise ValueError(f'Cannot section an edge less than twice {cfgid}: {sections}')
        edge = single(cfg.edges(source_id=source_id, target_id=target_id))
        section_depth = int(edge.depth / sections)
        if section_depth == 0:
            raise ValueError(f'Too many sections, results in 0-length section {cfgid}: {sections}')
        orig_depth = edge.depth
        new_depth = section_depth
        new_nodes = []
        curr_node_id = edge.source.id
        while new_depth < orig_depth:
            _LOGGER.info(f'Taking {section_depth} steps from node {cfgid}: {shorten_hashes(curr_node_id)}')
            cfg, curr_node_id = self.step(cfgid, cfg, curr_node_id, depth=section_depth)
            new_nodes.append(curr_node_id)
            new_depth += section_depth
        return (cfg, tuple(new_nodes))

    def all_path_reachability_prove(
        self,
        cfgid: str,
        cfg: KCFG,
        cfg_dir: Optional[Path] = None,
        is_terminal: Optional[Callable[[CTerm], bool]] = None,
        extract_branches: Optional[Callable[[CTerm], Iterable[KInner]]] = None,
        max_iterations: Optional[int] = None,
        execute_depth: Optional[int] = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        simplify_init: bool = True,
        implication_every_block: bool = True,
    ) -> KCFG:
        def _write_cfg(_cfg: KCFG) -> None:
            if cfg_dir is not None:
                KCFGExplore.write_cfg(cfgid, cfg_dir, _cfg)

        target_node = cfg.get_unique_target()
        iterations = 0

        while cfg.frontier:
            _write_cfg(cfg)

            if max_iterations is not None and max_iterations <= iterations:
                _LOGGER.warning(f'Reached iteration bound {cfgid}: {max_iterations}')
                break
            iterations += 1
            curr_node = cfg.frontier[0]

            if implication_every_block or (is_terminal is not None and is_terminal(curr_node.cterm)):
                _LOGGER.info(
                    f'Checking subsumption into target state {cfgid}: {shorten_hashes((curr_node.id, target_node.id))}'
                )
                csubst = self.cterm_implies(curr_node.cterm, target_node.cterm)
                if csubst is not None:
                    cfg.create_cover(curr_node.id, target_node.id, csubst=csubst)
                    _LOGGER.info(f'Subsumed into target node {cfgid}: {shorten_hashes((curr_node.id, target_node.id))}')
                    continue

            if is_terminal is not None:
                _LOGGER.info(f'Checking terminal {cfgid}: {shorten_hashes(curr_node.id)}')
                if is_terminal(curr_node.cterm):
                    _LOGGER.info(f'Terminal node {cfgid}: {shorten_hashes(curr_node.id)}.')
                    cfg.add_expanded(curr_node.id)
                    continue

            cfg.add_expanded(curr_node.id)

            _LOGGER.info(f'Advancing proof from node {cfgid}: {shorten_hashes(curr_node.id)}')
            depth, cterm, next_cterms = self.cterm_execute(
                curr_node.cterm, depth=execute_depth, cut_point_rules=cut_point_rules, terminal_rules=terminal_rules
            )

            # Nonsense case.
            if len(next_cterms) == 1:
                raise ValueError(f'Found a single successor cterm {cfgid}: {(depth, cterm, next_cterms)}')

            if depth > 0:
                next_node = cfg.get_or_create_node(cterm)
                cfg.create_edge(curr_node.id, next_node.id, depth)
                _LOGGER.info(
                    f'Found basic block at depth {depth} for {cfgid}: {shorten_hashes((curr_node.id, next_node.id))}.'
                )
                curr_node = next_node

            if len(next_cterms) == 0:
                _LOGGER.info(f'Found stuck node {cfgid}: {shorten_hashes(curr_node.id)}')

            else:
                branches = list(extract_branches(cterm)) if extract_branches is not None else []
                if len(branches) != len(next_cterms):
                    _LOGGER.warning(f'Falling back to manual branch extraction {cfgid}: {shorten_hashes(curr_node.id)}')
                    branches = [mlAnd(c for c in s.constraints if c not in cterm.constraints) for s in next_cterms]
                _LOGGER.info(
                    f'Found {len(branches)} branches for node {cfgid}: {shorten_hashes(curr_node.id)}: {[self.kprint.pretty_print(bc) for bc in branches]}'
                )
                cfg.split_on_constraints(curr_node.id, branches)

        _write_cfg(cfg)
        return cfg
