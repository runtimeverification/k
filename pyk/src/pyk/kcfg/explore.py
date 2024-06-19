from __future__ import annotations

import logging
from functools import cached_property
from typing import TYPE_CHECKING

from ..kast.inner import KApply, KVariable
from ..kast.manip import (
    flatten_label,
    minimize_term,
    ml_pred_to_bool,
    no_cell_rewrite_to_dots,
    push_down_rewrites,
    replace_rewrites_with_implies,
)
from ..kast.pretty import PrettyPrinter
from ..kore.rpc import LogRewrite, RewriteSuccess
from ..prelude.ml import is_top, mlAnd
from ..utils import not_none, shorten_hashes, single, unique
from .kcfg import KCFG, Abstract, Branch, NDBranch, Step, Stuck, Vacuous
from .semantics import DefaultSemantics

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from ..cterm import CTerm, CTermSymbolic
    from ..kast import KInner
    from ..kcfg.exploration import KCFGExploration
    from ..kore.rpc import LogEntry
    from .kcfg import KCFGExtendResult, NodeIdLike
    from .semantics import KCFGSemantics


_LOGGER: Final = logging.getLogger(__name__)


class KCFGExplore:
    cterm_symbolic: CTermSymbolic

    kcfg_semantics: KCFGSemantics
    id: str

    def __init__(
        self,
        cterm_symbolic: CTermSymbolic,
        *,
        kcfg_semantics: KCFGSemantics | None = None,
        id: str | None = None,
    ):
        self.cterm_symbolic = cterm_symbolic
        self.kcfg_semantics = kcfg_semantics if kcfg_semantics is not None else DefaultSemantics()
        self.id = id if id is not None else 'NO ID'

    @cached_property
    def _pretty_printer(self) -> PrettyPrinter:
        return PrettyPrinter(self.cterm_symbolic._definition)

    def pretty_print(self, kinner: KInner) -> str:
        return self._pretty_printer.print(kinner)

    def _extract_rule_labels(self, _logs: tuple[LogEntry, ...]) -> list[str]:
        _rule_lines = []
        for node_log in _logs:
            if isinstance(node_log, LogRewrite) and isinstance(node_log.result, RewriteSuccess):
                if node_log.result.rule_id in self.cterm_symbolic._definition.sentence_by_unique_id:
                    sent = self.cterm_symbolic._definition.sentence_by_unique_id[node_log.result.rule_id]
                    _rule_lines.append(f'{sent.label}:{sent.source}')
                else:
                    if node_log.result.rule_id == 'UNKNOWN':
                        _LOGGER.warning(f'Unknown unique id attached to rule log entry: {node_log}')
                    _rule_lines.append(f'{node_log.result.rule_id}:UNKNOWN')
        return _rule_lines

    def implication_failure_reason(self, antecedent: CTerm, consequent: CTerm) -> tuple[bool, str]:
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

        cterm_implies = self.cterm_symbolic.implies(antecedent, consequent, failure_reason=True)
        if cterm_implies.csubst is not None:
            return (True, '')

        failing_cells_strs = []
        for name, failing_cell in cterm_implies.failing_cells:
            failing_cell = push_down_rewrites(failing_cell)
            failing_cell = no_cell_rewrite_to_dots(failing_cell)
            failing_cell = replace_rewrites_with_implies(failing_cell)
            failing_cells_strs.append(f'{name}: {self.pretty_print(minimize_term(failing_cell))}')

        ret_str = 'Matching failed.'
        if len(failing_cells_strs) > 0:
            failing_cells_str = '\n'.join(failing_cells_strs)
            ret_str = f'{ret_str}\nThe following cells failed matching individually (antecedent #Implies consequent):\n{failing_cells_str}'

        if cterm_implies.remaining_implication is not None:
            ret_str = (
                f'{ret_str}\nThe remaining implication is:\n{self.pretty_print(cterm_implies.remaining_implication)}'
            )

            if cterm_implies.csubst is not None and not is_top(cterm_implies.remaining_implication):
                negative_cell_constraints = list(filter(_is_negative_cell_subst, antecedent.constraints))

                if len(negative_cell_constraints) > 0:
                    negative_cell_constraints_str = '\n'.join(self.pretty_print(cc) for cc in negative_cell_constraints)
                    ret_str = f'{ret_str}\nNegated cell substitutions found (consider using _ => ?_):\n{negative_cell_constraints_str}'

        return (False, ret_str)

    def simplify(self, cfg: KCFG, logs: dict[int, tuple[LogEntry, ...]]) -> None:
        for node in cfg.nodes:
            _LOGGER.info(f'Simplifying node {self.id}: {shorten_hashes(node.id)}')
            new_term, next_node_logs = self.cterm_symbolic.simplify(node.cterm)
            if new_term != node.cterm:
                cfg.let_node(node.id, cterm=new_term)
                if node.id in logs:
                    logs[node.id] += next_node_logs
                else:
                    logs[node.id] = next_node_logs

    def step(
        self,
        cfg: KCFG,
        node_id: NodeIdLike,
        logs: dict[int, tuple[LogEntry, ...]],
        depth: int = 1,
        module_name: str | None = None,
    ) -> int:
        if depth <= 0:
            raise ValueError(f'Expected positive depth, got: {depth}')
        node = cfg.node(node_id)
        successors = list(cfg.successors(node.id))
        if len(successors) != 0 and type(successors[0]) is KCFG.Split:
            raise ValueError(f'Cannot take step from split node {self.id}: {shorten_hashes(node.id)}')
        _LOGGER.info(f'Taking {depth} steps from node {self.id}: {shorten_hashes(node.id)}')
        exec_res = self.cterm_symbolic.execute(node.cterm, depth=depth, module_name=module_name)
        if exec_res.depth != depth:
            raise ValueError(f'Unable to take {depth} steps from node, got {exec_res.depth} steps {self.id}: {node.id}')
        if len(exec_res.next_states) > 0:
            raise ValueError(f'Found branch within {depth} steps {self.id}: {node.id}')
        new_node = cfg.create_node(exec_res.state)
        _LOGGER.info(f'Found new node at depth {depth} {self.id}: {shorten_hashes((node.id, new_node.id))}')
        logs[new_node.id] = exec_res.logs
        out_edges = cfg.edges(source_id=node.id)
        rule_logs = self._extract_rule_labels(exec_res.logs)
        if len(out_edges) == 0:
            cfg.create_edge(node.id, new_node.id, depth=depth, rules=rule_logs)
        else:
            edge = out_edges[0]
            if depth > edge.depth:
                raise ValueError(
                    f'Step depth {depth} greater than original edge depth {edge.depth} {self.id}: {shorten_hashes((edge.source.id, edge.target.id))}'
                )
            cfg.remove_edge(edge.source.id, edge.target.id)
            cfg.create_edge(edge.source.id, new_node.id, depth=depth, rules=rule_logs)
            cfg.create_edge(new_node.id, edge.target.id, depth=(edge.depth - depth), rules=edge.rules[depth:])
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
            curr_node_id = self.step(cfg, curr_node_id, logs, depth=section_depth)
            new_nodes.append(curr_node_id)
            new_depth += section_depth
        return tuple(new_nodes)

    def check_extendable(self, kcfg_exploration: KCFGExploration, node: KCFG.Node) -> None:
        kcfg: KCFG = kcfg_exploration.kcfg
        if not kcfg.is_leaf(node.id):
            raise ValueError(f'Cannot extend non-leaf node {self.id}: {node.id}')
        if kcfg.is_stuck(node.id):
            raise ValueError(f'Cannot extend stuck node {self.id}: {node.id}')
        if kcfg.is_vacuous(node.id):
            raise ValueError(f'Cannot extend vacuous node {self.id}: {node.id}')
        if kcfg_exploration.is_terminal(node.id):
            raise ValueError(f'Cannot extend terminal node {self.id}: {node.id}')

    def extend_cterm(
        self,
        _cterm: CTerm,
        node_id: int,
        *,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        module_name: str | None = None,
    ) -> KCFGExtendResult:
        def log(message: str, *, warning: bool = False) -> None:
            _LOGGER.log(logging.WARNING if warning else logging.INFO, f'Extend result for {self.id}: {message}')

        custom_step_result = self.kcfg_semantics.custom_step(_cterm)
        if custom_step_result is not None:
            log(f'custom step node: {node_id}')
            return custom_step_result

        abstract_cterm = self.kcfg_semantics.abstract_node(_cterm)
        if _cterm != abstract_cterm:
            log(f'abstraction node: {node_id}')
            return Abstract(abstract_cterm)

        cterm, next_states, depth, vacuous, next_node_logs = self.cterm_symbolic.execute(
            _cterm,
            depth=execute_depth,
            cut_point_rules=cut_point_rules,
            terminal_rules=terminal_rules,
            module_name=module_name,
        )

        # Basic block
        if depth > 0:
            log(f'basic block at depth {depth}: {node_id}')
            return Step(cterm, depth, next_node_logs, self._extract_rule_labels(next_node_logs))

        # Stuck or vacuous
        if not next_states:
            if vacuous:
                log(f'vacuous node: {node_id}', warning=True)
                return Vacuous()
            log(f'stuck node: {node_id}')
            return Stuck()

        # Cut rule
        if len(next_states) == 1:
            log(f'cut-rule basic block at depth {depth}: {node_id}')
            return Step(
                next_states[0].state,
                1,
                next_node_logs,
                self._extract_rule_labels(next_node_logs),
                cut=True,
            )

        # Branch
        assert len(next_states) > 1
        if all(branch_constraint for _, branch_constraint in next_states):
            branch_preds = [flatten_label('#And', not_none(rule_predicate)) for _, rule_predicate in next_states]
            common_preds = list(
                unique(
                    pred
                    for branch_pred in branch_preds
                    for pred in branch_pred
                    if all(pred in bp for bp in branch_preds)
                )
            )
            branches = [mlAnd(pred for pred in branch_pred if pred not in common_preds) for branch_pred in branch_preds]
            if common_preds:
                log(
                    f'Common predicates found in branches: {[self.pretty_print(ml_pred_to_bool(cp)) for cp in common_preds]}'
                )
            constraint_strs = [self.pretty_print(ml_pred_to_bool(bc)) for bc in branches]
            log(f'{len(branches)} branches: {node_id} -> {constraint_strs}')
            return Branch(branches)
        else:
            # NDBranch
            log(f'{len(next_states)} non-deterministic branches: {node_id}')
            next_cterms = [cterm for cterm, _ in next_states]
            return NDBranch(next_cterms, next_node_logs, self._extract_rule_labels(next_node_logs))
