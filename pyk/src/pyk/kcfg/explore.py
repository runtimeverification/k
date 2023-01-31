import json
import logging
from pathlib import Path
from typing import Any, Callable, ContextManager, Dict, Final, Iterable, List, Optional, Tuple, Union

from pyk.cli_utils import BugReport
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KLabel, KVariable, Subst
from pyk.kast.manip import flatten_label, free_vars
from pyk.kore.rpc import KoreClient, KoreServer
from pyk.kore.syntax import Top
from pyk.ktool import KPrint
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.ml import is_bottom, is_top, mlAnd, mlEquals, mlTop
from pyk.utils import hash_str, shorten_hashes, single

from .kcfg import KCFG

_LOGGER: Final = logging.getLogger(__name__)


class KCFGExplore(ContextManager['KCFGExplore']):
    kprint: KPrint
    _port: int
    _kore_rpc_command: Union[str, Iterable[str]] = 'kore-rpc'
    _kore_server: Optional[KoreServer]
    _kore_client: Optional[KoreClient]
    _rpc_closed: bool
    _bug_report: Optional[BugReport]

    def __init__(
        self,
        kprint: KPrint,
        port: int,
        bug_report: Optional[BugReport] = None,
        kore_rpc_command: Union[str, Iterable[str]] = 'kore-rpc',
    ):
        self.kprint = kprint
        self._port = port
        self._bug_report = bug_report
        self._kore_rpc_command = kore_rpc_command
        self._kore_server = None
        self._kore_client = None
        self._rpc_closed = False

    def __enter__(self) -> 'KCFGExplore':
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
                self._port,
                bug_report=self._bug_report,
                command=self._kore_rpc_command,
            )
        if not self._kore_client:
            self._kore_client = KoreClient('localhost', self._port, bug_report=self._bug_report)
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
        assume_defined: bool = True,
    ) -> Tuple[int, CTerm, List[CTerm]]:
        if assume_defined:
            cterm = cterm.add_constraint(
                KApply(KLabel('#Ceil', [GENERATED_TOP_CELL, GENERATED_TOP_CELL]), [cterm.kast])
            )
        _LOGGER.debug(f'Executing: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        er = kore_client.execute(kore, max_depth=depth, cut_point_rules=cut_point_rules, terminal_rules=terminal_rules)
        depth = er.depth
        next_state = CTerm(self.kprint.kore_to_kast(er.state.kore))
        _next_states = er.next_states if er.next_states is not None and len(er.next_states) > 1 else []
        next_states = [CTerm(self.kprint.kore_to_kast(ns.kore)) for ns in _next_states]
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
    ) -> Optional[Tuple[Subst, KInner]]:
        _LOGGER.debug(f'Checking implication: {antecedent} #Implies {consequent}')
        _consequent = consequent.kast
        if bind_consequent_variables:
            _consequent = consequent.kast
            fv_antecedent = free_vars(antecedent.kast)
            unbound_consequent = [v for v in free_vars(_consequent) if v not in fv_antecedent]
            if len(unbound_consequent) > 0:
                _LOGGER.info(f'Binding variables in consequent: {unbound_consequent}')
                for uc in unbound_consequent:
                    _consequent = KApply(KLabel('#Exists', [GENERATED_TOP_CELL]), [KVariable(uc), _consequent])
        antecedent_kore = self.kprint.kast_to_kore(antecedent.kast, GENERATED_TOP_CELL)
        consequent_kore = self.kprint.kast_to_kore(_consequent, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        result = kore_client.implies(antecedent_kore, consequent_kore)
        if type(result.implication) is not Top:
            _LOGGER.info(
                f'Received a non-trivial implication back from check implication endpoint: {result.implication}'
            )
        if result.substitution is None:
            return None
        ml_subst = self.kprint.kore_to_kast(result.substitution)
        ml_pred = self.kprint.kore_to_kast(result.predicate) if result.predicate is not None else mlTop()
        if is_top(ml_subst):
            return (Subst({}), ml_pred)
        subst_pattern = mlEquals(KVariable('###VAR'), KVariable('###TERM'))
        _subst: Dict[str, KInner] = {}
        for subst_pred in flatten_label('#And', ml_subst):
            m = subst_pattern.match(subst_pred)
            if m is not None and type(m['###VAR']) is KVariable:
                _subst[m['###VAR'].name] = m['###TERM']
            else:
                raise AssertionError(f'Received a non-substitution from implies endpoint: {subst_pred}')
        # TODO: remove this extra consequent checking logic or this comment after resolution: https://github.com/runtimeverification/haskell-backend/issues/3469
        new_consequent = self.cterm_simplify(CTerm(Subst(_subst)(consequent.add_constraint(ml_pred).kast)))
        if is_bottom(new_consequent):
            _LOGGER.warning(f'Simplifying instantiated consquent resulted in #Bottom: {antecedent} -> {consequent}')
            return None
        return (Subst(_subst), ml_pred)

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

    def step(self, cfgid: str, cfg: KCFG, node_id: str) -> Tuple[KCFG, str]:
        node = cfg.node(node_id)
        out_edges = cfg.edges(source_id=node.id)
        if len(out_edges) > 1:
            raise ValueError(
                f'Only support stepping from nodes with 0 or 1 out edges {cfgid}: {(node.id, [e.target.id for e in out_edges])}'
            )
        _LOGGER.info(f'Taking 1 step from node {cfgid}: {shorten_hashes(node.id)}')
        depth, cterm, next_cterms = self.cterm_execute(node.cterm, depth=1)
        if depth != 1:
            raise ValueError(f'Unable to take single step from node {cfgid}: {node.id}')
        if len(next_cterms) > 0:
            raise ValueError(f'Found branch with single step {cfgid}: {node.id}')
        new_node = cfg.get_or_create_node(cterm)
        _LOGGER.info(f'Found new node at depth 1 {cfgid}: {shorten_hashes((node.id, new_node.id))}')
        if len(out_edges) == 0:
            cfg.create_edge(node.id, new_node.id, condition=mlTop(), depth=1)
        else:
            edge = out_edges[0]
            cfg.remove_edge(edge.source.id, edge.target.id)
            cfg.create_edge(edge.source.id, new_node.id, condition=mlTop(), depth=1)
            cfg.create_edge(new_node.id, edge.target.id, condition=edge.condition, depth=(edge.depth - 1))
        return (cfg, new_node.id)

    def section_edge(
        self, cfgid: str, cfg: KCFG, source_id: str, target_id: str, sections: int = 2
    ) -> Tuple[KCFG, Tuple[str, ...]]:
        if sections <= 1:
            raise ValueError(f'Cannot section an edge less than twice: {sections}')
        edge = single(cfg.edges(source_id=source_id, target_id=target_id))
        if not is_top(edge.condition):
            raise ValueError(f'Cannot section edge with non-#Top condition: {edge.condition}')
        section_depth = int(edge.depth / sections)
        if section_depth == 0:
            raise ValueError(f'Too many sections, results in 0-length section: {sections}')
        cfg.remove_edge(source_id=source_id, target_id=target_id)
        remainder_depth = edge.depth - (section_depth * sections)
        if remainder_depth > 0:
            sections += 1
        else:
            remainder_depth = section_depth
        curr_node = edge.source
        new_nodes = []
        for _i in range(sections - 1):
            _LOGGER.info(f'Taking {section_depth} steps from node {cfgid}: {shorten_hashes(curr_node.id)}')
            new_depth, cterm, next_cterms = self.cterm_execute(curr_node.cterm, depth=section_depth)
            if new_depth != section_depth:
                raise ValueError(
                    f'Found section with differing depth than section depth: {new_depth} vs {section_depth}'
                )
            if len(next_cterms) != 0:
                raise ValueError('Found branch when sectioning edge.')
            new_node = cfg.get_or_create_node(cterm)
            new_nodes.append(new_node.id)
            _LOGGER.info(
                f'Found new node at {section_depth} steps from node {cfgid}: {shorten_hashes((curr_node.id, new_node.id))}'
            )
            cfg.create_edge(curr_node.id, new_node.id, condition=mlTop(), depth=section_depth)
            curr_node = new_node
        cfg.create_edge(source_id=curr_node.id, target_id=edge.target.id, condition=mlTop(), depth=remainder_depth)
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
                _LOGGER.warning(f'Reached iteration bound: {max_iterations}')
                break
            iterations += 1
            curr_node = cfg.frontier[0]

            if implication_every_block or (is_terminal is not None and is_terminal(curr_node.cterm)):
                _LOGGER.info(
                    f'Checking subsumption into target state {cfgid}: {shorten_hashes((curr_node.id, target_node.id))}'
                )
                impl = self.cterm_implies(curr_node.cterm, target_node.cterm)
                if impl is not None:
                    subst, pred = impl
                    cfg.create_cover(curr_node.id, target_node.id, subst=subst, constraint=pred)
                    _LOGGER.info(f'Subsumed into target node: {shorten_hashes((curr_node.id, target_node.id))}')
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
                raise ValueError(f'Found a single successor cterm: {(depth, cterm, next_cterms)}')

            if len(next_cterms) == 0 and depth == 0:
                _LOGGER.info(f'Found stuck node {cfgid}: {shorten_hashes(curr_node.id)}')
                continue

            if depth > 0:
                next_node = cfg.get_or_create_node(cterm)
                cfg.create_edge(curr_node.id, next_node.id, mlTop(), depth)
                _LOGGER.info(
                    f'Found basic block at depth {depth} for {cfgid}: {shorten_hashes((curr_node.id, next_node.id))}.'
                )

                branches = extract_branches(cterm) if extract_branches is not None else []
                if len(list(branches)) > 0:
                    cfg.add_expanded(next_node.id)
                    _LOGGER.info(
                        f'Found {len(list(branches))} branches {cfgid}: {[self.kprint.pretty_print(b) for b in branches]}'
                    )
                    splits = cfg.split_node(next_node.id, branches)
                    _LOGGER.info(f'Made split for {cfgid}: {shorten_hashes((next_node.id, splits))}')
                    continue

            else:
                _LOGGER.warning(f'Falling back to manual branch extraction {cfgid}: {shorten_hashes(curr_node.id)}')
                branch_constraints = [
                    mlAnd(c for c in s.constraints if c not in cterm.constraints) for s in next_cterms
                ]
                _LOGGER.info(
                    f'Found {len(list(next_cterms))} branches manually at depth 1 for {cfgid}: {[self.kprint.pretty_print(bc) for bc in branch_constraints]}'
                )
                for bs, bc in zip(next_cterms, branch_constraints):
                    branch_node = cfg.get_or_create_node(bs)
                    cfg.create_edge(curr_node.id, branch_node.id, bc, 1)

        _write_cfg(cfg)
        return cfg
