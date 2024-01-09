from __future__ import annotations

import logging
from abc import ABC
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NamedTuple, final

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
from ..kast.outer import KRule
from ..konvert import krule_to_kore
from ..kore.rpc import AbortedResult, SatResult, StopReason, UnknownResult, UnsatResult
from ..kore.syntax import Import, Module
from ..prelude import k
from ..prelude.k import GENERATED_TOP_CELL
from ..prelude.kbool import notBool
from ..prelude.kint import leInt, ltInt
from ..prelude.ml import is_top, mlAnd, mlEquals, mlEqualsFalse, mlEqualsTrue, mlImplies, mlNot, mlTop
from ..utils import shorten_hashes, single
from .kcfg import KCFG
from .semantics import DefaultSemantics

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from ..kast import KInner
    from ..kast.outer import KClaim
    from ..kcfg.exploration import KCFGExploration
    from ..kore.rpc import KoreClient, LogEntry
    from ..kore.syntax import Sentence
    from ..ktool.kprint import KPrint
    from .kcfg import NodeIdLike
    from .semantics import KCFGSemantics


_LOGGER: Final = logging.getLogger(__name__)


class CTermExecute(NamedTuple):
    state: CTerm
    next_states: tuple[CTerm, ...]
    depth: int
    vacuous: bool
    logs: tuple[LogEntry, ...]


class KCFGExplore:
    kprint: KPrint
    _kore_client: KoreClient

    kcfg_semantics: KCFGSemantics
    id: str
    _trace_rewrites: bool

    def __init__(
        self,
        kprint: KPrint,
        kore_client: KoreClient,
        *,
        kcfg_semantics: KCFGSemantics | None = None,
        id: str | None = None,
        trace_rewrites: bool = False,
    ):
        self.kprint = kprint
        self._kore_client = kore_client
        self.kcfg_semantics = kcfg_semantics if kcfg_semantics is not None else DefaultSemantics()
        self.id = id if id is not None else 'NO ID'
        self._trace_rewrites = trace_rewrites

    def cterm_execute(
        self,
        cterm: CTerm,
        depth: int | None = None,
        cut_point_rules: Iterable[str] | None = None,
        terminal_rules: Iterable[str] | None = None,
        module_name: str | None = None,
    ) -> CTermExecute:
        _LOGGER.debug(f'Executing: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        response = self._kore_client.execute(
            kore,
            max_depth=depth,
            cut_point_rules=cut_point_rules,
            terminal_rules=terminal_rules,
            module_name=module_name,
            log_successful_rewrites=self._trace_rewrites,
            log_failed_rewrites=self._trace_rewrites,
            log_successful_simplifications=self._trace_rewrites,
            log_failed_simplifications=self._trace_rewrites,
        )

        if isinstance(response, AbortedResult):
            unknown_predicate = response.unknown_predicate.text if response.unknown_predicate else None
            raise ValueError(f'Backend responded with aborted state. Unknown predicate: {unknown_predicate}')

        state = CTerm.from_kast(self.kprint.kore_to_kast(response.state.kore))
        resp_next_states = response.next_states or ()
        next_states = tuple(CTerm.from_kast(self.kprint.kore_to_kast(ns.kore)) for ns in resp_next_states)

        assert all(not cterm.is_bottom for cterm in next_states)
        assert len(next_states) != 1 or response.reason is StopReason.CUT_POINT_RULE

        return CTermExecute(
            state=state,
            next_states=next_states,
            depth=response.depth,
            vacuous=response.reason is StopReason.VACUOUS,
            logs=response.logs,
        )

    def cterm_simplify(self, cterm: CTerm) -> tuple[CTerm, tuple[LogEntry, ...]]:
        _LOGGER.debug(f'Simplifying: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        kore_simplified, logs = self._kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        return CTerm.from_kast(kast_simplified), logs

    def kast_simplify(self, kast: KInner) -> tuple[KInner, tuple[LogEntry, ...]]:
        _LOGGER.debug(f'Simplifying: {kast}')
        kore = self.kprint.kast_to_kore(kast, GENERATED_TOP_CELL)
        kore_simplified, logs = self._kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        return kast_simplified, logs

    def cterm_get_model(self, cterm: CTerm, module_name: str | None = None) -> Subst | None:
        _LOGGER.info(f'Getting model: {cterm}')
        kore = self.kprint.kast_to_kore(cterm.kast, GENERATED_TOP_CELL)
        result = self._kore_client.get_model(kore, module_name=module_name)
        if type(result) is UnknownResult:
            _LOGGER.debug('Result is Unknown')
            return None
        elif type(result) is UnsatResult:
            _LOGGER.debug('Result is UNSAT')
            return None
        elif type(result) is SatResult:
            _LOGGER.debug('Result is SAT')
            if not result.model:
                return Subst({})
            model_subst = self.kprint.kore_to_kast(result.model)
            try:
                return Subst.from_pred(model_subst)
            except ValueError as err:
                raise AssertionError(f'Received a non-substitution from get-model endpoint: {model_subst}') from err

        else:
            raise AssertionError('Received an invalid response from get-model endpoint')

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
        result = self._kore_client.implies(antecedent_kore, consequent_kore)
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
        kore_simplified, _logs = self._kore_client.simplify(kore)
        kast_simplified = self.kprint.kore_to_kast(kore_simplified)
        _LOGGER.debug(f'Definedness condition computed: {kast_simplified}')
        return cterm.add_constraint(kast_simplified)

    def simplify(self, cfg: KCFG, logs: dict[int, tuple[LogEntry, ...]]) -> None:
        for node in cfg.nodes:
            _LOGGER.info(f'Simplifying node {self.id}: {shorten_hashes(node.id)}')
            new_term, next_node_logs = self.cterm_simplify(node.cterm)
            if new_term != node.cterm:
                cfg.replace_node(node.id, new_term)
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
        exec_res = self.cterm_execute(node.cterm, depth=depth, module_name=module_name)
        if exec_res.depth != depth:
            raise ValueError(f'Unable to take {depth} steps from node, got {exec_res.depth} steps {self.id}: {node.id}')
        if len(exec_res.next_states) > 0:
            raise ValueError(f'Found branch within {depth} steps {self.id}: {node.id}')
        new_node = cfg.create_node(exec_res.state)
        _LOGGER.info(f'Found new node at depth {depth} {self.id}: {shorten_hashes((node.id, new_node.id))}')
        logs[new_node.id] = exec_res.logs
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

    def extend(
        self,
        kcfg_exploration: KCFGExploration,
        node: KCFG.Node,
        logs: dict[int, tuple[LogEntry, ...]],
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        module_name: str | None = None,
    ) -> None:
        self.check_extendable(kcfg_exploration, node)
        extend_result = self.extend_cterm(
            node.cterm,
            execute_depth=execute_depth,
            cut_point_rules=cut_point_rules,
            terminal_rules=terminal_rules,
            module_name=module_name,
        )
        self.extend_kcfg(extend_result, kcfg_exploration.kcfg, node, logs)

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
        *,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        module_name: str | None = None,
    ) -> ExtendResult:
        abstract_cterm = self.kcfg_semantics.abstract_node(_cterm)
        if _cterm != abstract_cterm:
            return Abstract(abstract_cterm)

        _branches = self.kcfg_semantics.extract_branches(_cterm)
        branches = []
        for constraint in _branches:
            kast = mlAnd(list(_cterm.constraints) + [constraint])
            kast, _ = self.kast_simplify(kast)
            if not CTerm._is_bottom(kast):
                branches.append(constraint)
        if len(branches) > 1:
            return Branch(branches, heuristic=True)

        cterm, next_cterms, depth, vacuous, next_node_logs = self.cterm_execute(
            _cterm,
            depth=execute_depth,
            cut_point_rules=cut_point_rules,
            terminal_rules=terminal_rules,
            module_name=module_name,
        )

        # Basic block
        if depth > 0:
            return Step(cterm, depth, next_node_logs)

        # Stuck or vacuous
        if not next_cterms:
            if vacuous:
                return Vacuous()
            return Stuck()

        # Cut rule
        if len(next_cterms) == 1:
            return Step(next_cterms[0], 1, next_node_logs, cut=True)

        # Branch
        assert len(next_cterms) > 1
        branches = [mlAnd(c for c in s.constraints if c not in cterm.constraints) for s in next_cterms]
        branch_and = mlAnd(branches)
        branch_patterns = [
            mlAnd([mlEqualsTrue(KVariable('B')), mlEqualsTrue(notBool(KVariable('B')))]),
            mlAnd([mlEqualsTrue(notBool(KVariable('B'))), mlEqualsTrue(KVariable('B'))]),
            mlAnd([mlEqualsTrue(KVariable('B')), mlEqualsFalse(KVariable('B'))]),
            mlAnd([mlEqualsFalse(KVariable('B')), mlEqualsTrue(KVariable('B'))]),
            mlAnd([mlNot(KVariable('B')), KVariable('B')]),
            mlAnd([KVariable('B'), mlNot(KVariable('B'))]),
            mlAnd(
                [
                    mlEqualsTrue(ltInt(KVariable('I1'), KVariable('I2'))),
                    mlEqualsTrue(leInt(KVariable('I2'), KVariable('I1'))),
                ]
            ),
            mlAnd(
                [
                    mlEqualsTrue(leInt(KVariable('I1'), KVariable('I2'))),
                    mlEqualsTrue(ltInt(KVariable('I2'), KVariable('I1'))),
                ]
            ),
        ]

        # Split on branch patterns
        if any(branch_pattern.match(branch_and) for branch_pattern in branch_patterns):
            return Branch(branches)

        # NDBranch on successor nodes
        return NDBranch(next_cterms, next_node_logs)

    def extend_kcfg(
        self,
        extend_result: ExtendResult,
        kcfg: KCFG,
        node: KCFG.Node,
        logs: dict[int, tuple[LogEntry, ...]],
    ) -> None:
        def log(message: str, *, warning: bool = False) -> None:
            _LOGGER.log(logging.WARNING if warning else logging.INFO, f'Extend result for {self.id}: {message}')

        match extend_result:
            case Vacuous():
                kcfg.add_vacuous(node.id)
                log(f'vacuous node: {node.id}', warning=True)

            case Stuck():
                kcfg.add_stuck(node.id)
                log(f'stuck node: {node.id}')

            case Abstract(cterm):
                new_node = kcfg.create_node(cterm)
                kcfg.create_cover(node.id, new_node.id)
                log(f'abstraction node: {node.id} -> {new_node.id}')

            case Step(cterm, depth, next_node_logs, cut):
                next_node = kcfg.create_node(cterm)
                logs[next_node.id] = next_node_logs
                kcfg.create_edge(node.id, next_node.id, depth)
                cut_str = 'cut-rule ' if cut else ''
                log(f'{cut_str}basic block at depth {depth}: {node.id} -> {next_node.id}')

            case Branch(constraints, heuristic):
                kcfg.split_on_constraints(node.id, constraints)
                heur_str = ' using heuristics' if heuristic else ''
                constraint_strs = [self.kprint.pretty_print(bc) for bc in constraints]
                log(f'{len(constraints)} branches{heur_str}: {node.id} -> {constraint_strs}')

            case NDBranch(cterms, next_node_logs):
                next_ids = [kcfg.create_node(cterm).id for cterm in cterms]
                for i in next_ids:
                    logs[i] = next_node_logs
                kcfg.create_ndbranch(node.id, next_ids)
                log(f'{len(next_ids)} non-deterministic branches: {node.id} -> {next_ids}')

            case _:
                raise AssertionError()

    def add_dependencies_module(
        self, old_module_name: str, new_module_name: str, dependencies: Iterable[KClaim], priority: int = 1
    ) -> None:
        kast_rules = [
            KRule(body=c.body, requires=c.requires, ensures=c.ensures, att=c.att.update({'priority': priority}))
            for c in dependencies
        ]
        kore_axioms: list[Sentence] = [
            krule_to_kore(self.kprint.definition, self.kprint.kompiled_kore, r) for r in kast_rules
        ]
        sentences: list[Sentence] = [Import(module_name=old_module_name, attrs=())]
        sentences = sentences + kore_axioms
        m = Module(name=new_module_name, sentences=sentences)
        _LOGGER.info(f'Adding dependencies module {self.id}: {new_module_name}')
        self._kore_client.add_module(m)


class ExtendResult(ABC):
    ...


@final
@dataclass(frozen=True)
class Vacuous(ExtendResult):
    ...


@final
@dataclass(frozen=True)
class Stuck(ExtendResult):
    ...


@final
@dataclass(frozen=True)
class Abstract(ExtendResult):
    cterm: CTerm


@final
@dataclass(frozen=True)
class Step(ExtendResult):
    cterm: CTerm
    depth: int
    logs: tuple[LogEntry, ...]
    cut: bool = field(default=False)


@final
@dataclass(frozen=True)
class Branch(ExtendResult):
    constraints: tuple[KInner, ...]
    heuristic: bool

    def __init__(self, constraints: Iterable[KInner], *, heuristic: bool = False):
        object.__setattr__(self, 'constraints', tuple(constraints))
        object.__setattr__(self, 'heuristic', heuristic)


@final
@dataclass(frozen=True)
class NDBranch(ExtendResult):
    cterms: tuple[CTerm, ...]
    logs: tuple[LogEntry, ...] = field(default=())

    def __init__(self, cterms: Iterable[CTerm], logs: Iterable[LogEntry,]):
        object.__setattr__(self, 'cterms', tuple(cterms))
        object.__setattr__(self, 'logs', tuple(logs))
