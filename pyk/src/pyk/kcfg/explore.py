from __future__ import annotations

import logging
from typing import TYPE_CHECKING, ContextManager

from ..cterm import CSubst, CTerm
from ..kast.inner import KApply, KLabel, KRewrite, KVariable, Subst
from ..kast.manip import (
    abstract_term_safely,
    bottom_up,
    extract_lhs,
    extract_rhs,
    flatten_label,
    free_vars,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
)
from ..kore.rpc import KoreClient, KoreServer, StopReason
from ..ktool.kprove import KoreExecLogFormat
from ..prelude import k
from ..prelude.k import GENERATED_TOP_CELL
from ..prelude.kbool import notBool
from ..prelude.ml import is_bottom, is_top, mlAnd, mlEquals, mlEqualsFalse, mlEqualsTrue, mlImplies, mlNot, mlTop
from ..utils import shorten_hashes, single
from .kcfg import KCFG

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Any, Final

    from ..cli_utils import BugReport
    from ..kast import KInner
    from ..kore.rpc import LogEntry
    from ..ktool.kprint import KPrint
    from .kcfg import NodeIdLike


_LOGGER: Final = logging.getLogger(__name__)


class KCFGExplore(ContextManager['KCFGExplore']):
    kprint: KPrint
    id: str
    _port: int | None
    _kore_rpc_command: str | Iterable[str]
    _smt_timeout: int | None
    _smt_retry_limit: int | None
    _bug_report: BugReport | None

    _kore_server: KoreServer | None
    _kore_client: KoreClient | None
    _rpc_closed: bool
    _trace_rewrites: bool

    def __init__(
        self,
        kprint: KPrint,
        *,
        id: str | None = None,
        port: int | None = None,
        kore_rpc_command: str | Iterable[str] = 'kore-rpc',
        smt_timeout: int | None = None,
        smt_retry_limit: int | None = None,
        bug_report: BugReport | None = None,
        haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Path | None = None,
        trace_rewrites: bool = False,
    ):
        self.kprint = kprint
        self.id = id if id is not None else 'NO ID'
        self._port = port
        self._kore_rpc_command = kore_rpc_command
        self._smt_timeout = smt_timeout
        self._smt_retry_limit = smt_retry_limit
        self._bug_report = bug_report
        self._haskell_log_format = haskell_log_format
        self._haskell_log_entries = haskell_log_entries
        self._log_axioms_file = log_axioms_file
        self._kore_server = None
        self._kore_client = None
        self._rpc_closed = False
        self._trace_rewrites = trace_rewrites

    def __enter__(self) -> KCFGExplore:
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    @property
    def _kore_rpc(self) -> tuple[KoreServer, KoreClient]:
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
                haskell_log_format=self._haskell_log_format,
                haskell_log_entries=self._haskell_log_entries,
                log_axioms_file=self._log_axioms_file,
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
        depth: int | None = None,
        cut_point_rules: Iterable[str] | None = None,
        terminal_rules: Iterable[str] | None = None,
    ) -> tuple[int, CTerm, list[CTerm], tuple[LogEntry, ...]]:
        _LOGGER.debug(f'Executing: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        er = kore_client.execute(
            kore,
            max_depth=depth,
            cut_point_rules=cut_point_rules,
            terminal_rules=terminal_rules,
            log_successful_rewrites=self._trace_rewrites,
            log_failed_rewrites=self._trace_rewrites,
            log_successful_simplifications=self._trace_rewrites,
            log_failed_simplifications=self._trace_rewrites,
        )
        depth = er.depth
        next_state = CTerm.from_kast(self.kprint.kore_to_kast(er.state.kore))
        _next_states = er.next_states if er.next_states is not None else []
        next_states = [CTerm.from_kast(self.kprint.kore_to_kast(ns.kore)) for ns in _next_states]
        if len(next_states) == 1 and len(next_states) < len(_next_states):
            return depth + 1, next_states[0], [], er.logs
        elif len(next_states) == 1:
            if er.reason == StopReason.CUT_POINT_RULE:
                return depth, next_state, next_states, er.logs
            else:
                next_states = []
        return depth, next_state, next_states, er.logs

    def cterm_simplify(self, cterm: CTerm) -> tuple[KInner, tuple[LogEntry, ...]]:
        _LOGGER.debug(f'Simplifying: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        kore_simplified, logs = kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        return kast_simplified, logs

    def cterm_implies(
        self,
        antecedent: CTerm,
        consequent: CTerm,
    ) -> CSubst | None:
        _LOGGER.debug(f'Checking implication: {antecedent} #Implies {consequent}')
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
        _subst: dict[str, KInner] = {}
        for subst_pred in flatten_label('#And', ml_subst):
            m = subst_pattern.match(subst_pred)
            if m is not None and type(m['###VAR']) is KVariable:
                _subst[m['###VAR'].name] = m['###TERM']
            else:
                raise AssertionError(f'Received a non-substitution from implies endpoint: {subst_pred}')
        return CSubst(subst=Subst(_subst), constraints=ml_preds)

    def implication_failure_reason(self, antecedent: CTerm, consequent: CTerm) -> tuple[bool, str]:
        def no_cell_rewrite_to_dots(term: KInner) -> KInner:
            def _no_cell_rewrite_to_dots(_term: KInner) -> KInner:
                if type(_term) is KApply and _term.is_cell:
                    lhs = extract_lhs(_term)
                    rhs = extract_rhs(_term)
                    if lhs == rhs:
                        return KApply(_term.label, [abstract_term_safely(lhs, base_name=_term.label.name)])
                return _term

            return bottom_up(_no_cell_rewrite_to_dots, term)

        def _is_cell_subst(csubst: KInner) -> bool:
            if type(csubst) is KApply and csubst.label.name == '_==K_':
                csubst_arg = csubst.args[0]
                if type(csubst_arg) is KVariable and csubst_arg.name.endswith('_CELL'):
                    return True
            return False

        def _is_negative_cell_subst(constraint: KInner) -> bool:
            constraint_bool = ml_pred_to_bool(constraint)
            if type(constraint_bool) is KApply and constraint_bool.label.name == 'notBool_':
                negative_constraint = constraint_bool.args[0]
                if type(negative_constraint) is KApply and negative_constraint.label.name == '_andBool_':
                    constraints = flatten_label('_andBool_', negative_constraint)
                    cell_constraints = list(filter(_is_cell_subst, constraints))
                    if len(cell_constraints) > 0:
                        return True
            return False

        def replace_rewrites_with_implies(kast: KInner) -> KInner:
            def _replace_rewrites_with_implies(_kast: KInner) -> KInner:
                if type(_kast) is KRewrite:
                    return mlImplies(_kast.lhs, _kast.rhs)
                return _kast

            return bottom_up(_replace_rewrites_with_implies, kast)

        config_match = self.cterm_implies(CTerm.from_kast(antecedent.config), CTerm.from_kast(consequent.config))
        if config_match is None:
            failing_cells = []
            curr_cell_match = Subst({})
            for cell in antecedent.cells:
                antecedent_cell = antecedent.cell(cell)
                consequent_cell = consequent.cell(cell)
                cell_match = consequent_cell.match(antecedent_cell)
                if cell_match is not None:
                    _curr_cell_match = curr_cell_match.union(cell_match)
                    if _curr_cell_match is not None:
                        curr_cell_match = _curr_cell_match
                        continue
                failing_cell = push_down_rewrites(KRewrite(antecedent_cell, consequent_cell))
                failing_cell = no_cell_rewrite_to_dots(failing_cell)
                failing_cell = replace_rewrites_with_implies(failing_cell)
                failing_cells.append((cell, failing_cell))
            failing_cells_str = '\n'.join(
                f'{cell}: {self.kprint.pretty_print(minimize_term(rew))}' for cell, rew in failing_cells
            )
            return (
                False,
                f'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\n{failing_cells_str}',
            )
        else:
            consequent_constraints = list(
                filter(lambda x: not CTerm._is_spurious_constraint(x), map(config_match.subst, consequent.constraints))
            )
            impl = CTerm._ml_impl(antecedent.constraints, consequent_constraints)
            if impl != mlTop(k.GENERATED_TOP_CELL):
                fail_str = self.kprint.pretty_print(impl)
                negative_cell_constraints = list(filter(_is_negative_cell_subst, antecedent.constraints))
                if len(negative_cell_constraints) > 0:
                    fail_str = (
                        f'{fail_str}\n\nNegated cell substitutions found (consider using _ => ?_):\n'
                        + '\n'.join([self.kprint.pretty_print(cc) for cc in negative_cell_constraints])
                    )
                return (False, f'Implication check failed, the following is the remaining implication:\n{fail_str}')
        return (True, '')

    def cterm_assume_defined(self, cterm: CTerm) -> CTerm:
        _LOGGER.debug(f'Computing definedness condition for: {cterm}')
        kast = KApply(KLabel('#Ceil', [GENERATED_TOP_CELL, GENERATED_TOP_CELL]), [cterm.config])
        kore = self.kprint.kast_to_kore(kast, GENERATED_TOP_CELL)
        _, kore_client = self._kore_rpc
        kore_simplified, _logs = kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        _LOGGER.debug(f'Definedness condition computed: {kast_simplified}')
        return cterm.add_constraint(kast_simplified)

    def remove_subgraph_from(self, cfg: KCFG, node: NodeIdLike) -> None:
        for _node in cfg.reachable_nodes(node, traverse_covers=True):
            if not cfg.is_target(_node.id):
                _LOGGER.info(f'Removing node: {shorten_hashes(_node.id)}')
                cfg.remove_node(_node.id)

    def simplify(self, cfg: KCFG, logs: dict[int, tuple[LogEntry, ...]]) -> None:
        for node in cfg.nodes:
            _LOGGER.info(f'Simplifying node {self.id}: {shorten_hashes(node.id)}')
            new_term, next_node_logs = self.cterm_simplify(node.cterm)
            if is_top(new_term):
                raise ValueError(f'Node simplified to #Top {self.id}: {shorten_hashes(node.id)}')
            if is_bottom(new_term):
                raise ValueError(f'Node simplified to #Bottom {self.id}: {shorten_hashes(node.id)}')
            if new_term != node.cterm.kast:
                cfg.replace_node(node.id, CTerm.from_kast(new_term))
                if node.id in logs:
                    logs[node.id] += next_node_logs
                else:
                    logs[node.id] = next_node_logs

    def step(self, cfg: KCFG, node_id: NodeIdLike, logs: dict[int, tuple[LogEntry, ...]], depth: int = 1) -> int:
        if depth <= 0:
            raise ValueError(f'Expected positive depth, got: {depth}')
        node = cfg.node(node_id)
        successors = list(cfg.successors(node.id))
        if len(successors) != 0 and type(successors[0]) is KCFG.Split:
            raise ValueError(f'Cannot take step from split node {self.id}: {shorten_hashes(node.id)}')
        _LOGGER.info(f'Taking {depth} steps from node {self.id}: {shorten_hashes(node.id)}')
        actual_depth, cterm, next_cterms, next_node_logs = self.cterm_execute(node.cterm, depth=depth)
        if actual_depth != depth:
            raise ValueError(f'Unable to take {depth} steps from node, got {actual_depth} steps {self.id}: {node.id}')
        if len(next_cterms) > 0:
            raise ValueError(f'Found branch within {depth} steps {self.id}: {node.id}')
        new_node = cfg.create_node(cterm)
        _LOGGER.info(f'Found new node at depth {depth} {self.id}: {shorten_hashes((node.id, new_node.id))}')
        logs[new_node.id] = next_node_logs
        out_edges = cfg.edges(source_id=node.id)
        if len(out_edges) == 0:
            cfg.create_edge(node.id, new_node.id, depth=depth)
        else:
            edge = out_edges[0]
            if depth > edge.depth:
                raise ValueError(
                    f'Step depth {depth} greater than original edge depth {edge.depth} {self.id}: {shorten_hashes((edge.source.id, edge.target.id))}'
                )
            cfg.remove_edge(edge.source.id, edge.target.id)
            cfg.create_edge(edge.source.id, new_node.id, depth=depth)
            cfg.create_edge(new_node.id, edge.target.id, depth=(edge.depth - depth))
        return new_node.id

    def section_edge(
        self,
        cfg: KCFG,
        source_id: NodeIdLike,
        target_id: NodeIdLike,
        logs: dict[int, tuple[LogEntry, ...]],
        sections: int = 2,
    ) -> tuple[int, ...]:
        if sections <= 1:
            raise ValueError(f'Cannot section an edge less than twice {self.id}: {sections}')
        edge = single(cfg.edges(source_id=source_id, target_id=target_id))
        section_depth = int(edge.depth / sections)
        if section_depth == 0:
            raise ValueError(f'Too many sections, results in 0-length section {self.id}: {sections}')
        orig_depth = edge.depth
        new_depth = section_depth
        new_nodes = []
        curr_node_id = edge.source.id
        while new_depth < orig_depth:
            _LOGGER.info(f'Taking {section_depth} steps from node {self.id}: {shorten_hashes(curr_node_id)}')
            curr_node_id = self.step(cfg, curr_node_id, logs, depth=section_depth)
            new_nodes.append(curr_node_id)
            new_depth += section_depth
        return tuple(new_nodes)

    def target_subsume(
        self,
        kcfg: KCFG,
        node: KCFG.Node,
    ) -> bool:
        target_node = kcfg.get_unique_target()
        _LOGGER.info(f'Checking subsumption into target state {self.id}: {shorten_hashes((node.id, target_node.id))}')
        csubst = self.cterm_implies(node.cterm, target_node.cterm)
        if csubst is not None:
            kcfg.create_cover(node.id, target_node.id, csubst=csubst)
            _LOGGER.info(f'Subsumed into target node {self.id}: {shorten_hashes((node.id, target_node.id))}')
            return True
        return False

    def extend(
        self,
        kcfg: KCFG,
        node: KCFG.Node,
        logs: dict[int, tuple[LogEntry, ...]],
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
    ) -> None:
        if not kcfg.is_frontier(node.id):
            raise ValueError(f'Cannot extend non-frontier node {self.id}: {node.id}')

        kcfg.add_expanded(node.id)

        _LOGGER.info(f'Extending KCFG from node {self.id}: {shorten_hashes(node.id)}')
        depth, cterm, next_cterms, next_node_logs = self.cterm_execute(
            node.cterm, depth=execute_depth, cut_point_rules=cut_point_rules, terminal_rules=terminal_rules
        )

        # Basic block
        if depth > 0:
            next_node = kcfg.create_node(cterm)
            logs[next_node.id] = next_node_logs
            kcfg.create_edge(node.id, next_node.id, depth)
            _LOGGER.info(
                f'Found basic block at depth {depth} for {self.id}: {shorten_hashes((node.id, next_node.id))}.'
            )

        # Stuck
        elif len(next_cterms) == 0:
            _LOGGER.info(f'Found stuck node {self.id}: {shorten_hashes(node.id)}')

        # Cut Rule
        elif len(next_cterms) == 1:
            next_node = kcfg.create_node(next_cterms[0])
            logs[next_node.id] = next_node_logs
            kcfg.create_edge(node.id, next_node.id, 1)
            _LOGGER.info(
                f'Inserted cut-rule basic block at depth 1 for {self.id}: {shorten_hashes((node.id, next_node.id))}'
            )

        # Branch
        elif len(next_cterms) > 1:
            branches = [mlAnd(c for c in s.constraints if c not in cterm.constraints) for s in next_cterms]
            branch_and = mlAnd(branches)
            branch_patterns = [
                mlAnd([mlEqualsTrue(KVariable('B')), mlEqualsTrue(notBool(KVariable('B')))]),
                mlAnd([mlEqualsTrue(notBool(KVariable('B'))), mlEqualsTrue(KVariable('B'))]),
                mlAnd([mlEqualsTrue(KVariable('B')), mlEqualsFalse(KVariable('B'))]),
                mlAnd([mlEqualsFalse(KVariable('B')), mlEqualsTrue(KVariable('B'))]),
                mlAnd([mlNot(KVariable('B')), KVariable('B')]),
                mlAnd([KVariable('B'), mlNot(KVariable('B'))]),
            ]

            # Split on branch patterns
            if any(branch_pattern.match(branch_and) for branch_pattern in branch_patterns):
                kcfg.split_on_constraints(node.id, branches)
                _LOGGER.info(
                    f'Found {len(branches)} branches for node {self.id}: {shorten_hashes(node.id)}: {[self.kprint.pretty_print(bc) for bc in branches]}'
                )

            # NDBranch on successor nodes
            else:
                next_ids = [kcfg.create_node(ct).id for ct in next_cterms]
                for i in next_ids:
                    logs[i] = next_node_logs
                kcfg.create_ndbranch(node.id, next_ids)
                _LOGGER.info(
                    f'Found {len(next_ids)} non-deterministic branches for node {self.id}: {shorten_hashes(node.id)}'
                )

        else:
            raise ValueError('Unhandled case.')
