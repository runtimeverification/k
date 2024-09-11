from __future__ import annotations

import logging
from contextlib import contextmanager
from dataclasses import dataclass
from typing import TYPE_CHECKING, NamedTuple, final

from pyk.utils import not_none

from ..cterm import CSubst, CTerm
from ..kast.inner import KApply, KLabel, KRewrite, KToken, KVariable, Subst
from ..kast.manip import flatten_label, is_spurious_constraint, sort_ac_collections
from ..kast.pretty import PrettyPrinter
from ..konvert import kast_to_kore, kore_to_kast
from ..kore.rpc import (
    AbortedResult,
    KoreClient,
    KoreExecLogFormat,
    SatResult,
    SmtSolverError,
    StopReason,
    TransportType,
    UnknownResult,
    UnsatResult,
    kore_server,
)
from ..prelude.k import GENERATED_TOP_CELL, K_ITEM
from ..prelude.ml import mlAnd

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from pathlib import Path
    from typing import Final

    from ..kast import KInner
    from ..kast.outer import KDefinition
    from ..kore.rpc import FallbackReason, LogEntry
    from ..kore.syntax import Pattern
    from ..utils import BugReport


_LOGGER: Final = logging.getLogger(__name__)


class NextState(NamedTuple):
    state: CTerm
    condition: KInner | None


class CTermExecute(NamedTuple):
    state: CTerm
    next_states: tuple[NextState, ...]
    depth: int
    vacuous: bool
    logs: tuple[LogEntry, ...]


class CTermImplies(NamedTuple):
    csubst: CSubst | None
    failing_cells: tuple[tuple[str, KInner], ...]
    remaining_implication: KInner | None
    logs: tuple[LogEntry, ...]


@final
@dataclass
class CTermSMTError(Exception):
    def __init__(self, message: str):
        super().__init__(message)
        self.message = message


class CTermSymbolic:
    _kore_client: KoreClient
    _definition: KDefinition
    _log_succ_rewrites: bool
    _log_fail_rewrites: bool

    def __init__(
        self,
        kore_client: KoreClient,
        definition: KDefinition,
        *,
        log_succ_rewrites: bool = True,
        log_fail_rewrites: bool = False,
    ):
        self._kore_client = kore_client
        self._definition = definition
        self._log_succ_rewrites = log_succ_rewrites
        self._log_fail_rewrites = log_fail_rewrites

    def kast_to_kore(self, kinner: KInner) -> Pattern:
        return kast_to_kore(self._definition, kinner, sort=GENERATED_TOP_CELL)

    def kore_to_kast(self, pattern: Pattern) -> KInner:
        return kore_to_kast(self._definition, pattern)

    def execute(
        self,
        cterm: CTerm,
        depth: int | None = None,
        cut_point_rules: Iterable[str] | None = None,
        terminal_rules: Iterable[str] | None = None,
        module_name: str | None = None,
    ) -> CTermExecute:

        _LOGGER.debug(f'Executing: {cterm}')
        kore = self.kast_to_kore(cterm.kast)
        try:
            response = self._kore_client.execute(
                kore,
                max_depth=depth,
                cut_point_rules=cut_point_rules,
                terminal_rules=terminal_rules,
                module_name=module_name,
                log_successful_rewrites=self._log_succ_rewrites,
                log_failed_rewrites=self._log_succ_rewrites and self._log_fail_rewrites,
            )
        except SmtSolverError as err:
            raise self._smt_solver_error(err) from err

        if isinstance(response, AbortedResult):
            unknown_predicate = response.unknown_predicate.text if response.unknown_predicate else None
            raise ValueError(f'Backend responded with aborted state. Unknown predicate: {unknown_predicate}')

        state = CTerm.from_kast(self.kore_to_kast(response.state.kore))
        resp_next_states = response.next_states or ()
        branching_constraints = tuple(
            self.kore_to_kast(not_none(s.rule_predicate)) if s.rule_predicate is not None else None
            for s in resp_next_states
        )
        next_states = tuple(
            NextState(CTerm.from_kast(self.kore_to_kast(ns.kore)), c)
            for ns, c in zip(resp_next_states, branching_constraints, strict=True)
        )

        assert all(not cterm.is_bottom for cterm, _ in next_states)
        assert len(next_states) != 1 or response.reason is StopReason.CUT_POINT_RULE

        return CTermExecute(
            state=state,
            next_states=next_states,
            depth=response.depth,
            vacuous=response.reason is StopReason.VACUOUS,
            logs=response.logs,
        )

    def simplify(self, cterm: CTerm, module_name: str | None = None) -> tuple[CTerm, tuple[LogEntry, ...]]:
        _LOGGER.debug(f'Simplifying: {cterm}')
        kast_simplified, logs = self.kast_simplify(cterm.kast, module_name=module_name)
        return CTerm.from_kast(kast_simplified), logs

    def kast_simplify(self, kast: KInner, module_name: str | None = None) -> tuple[KInner, tuple[LogEntry, ...]]:
        _LOGGER.debug(f'Simplifying: {kast}')
        kore = self.kast_to_kore(kast)
        try:
            kore_simplified, logs = self._kore_client.simplify(kore, module_name=module_name)
        except SmtSolverError as err:
            raise self._smt_solver_error(err) from err

        kast_simplified = self.kore_to_kast(kore_simplified)
        return kast_simplified, logs

    def get_model(self, cterm: CTerm, module_name: str | None = None) -> Subst | None:
        _LOGGER.debug(f'Getting model: {cterm}')
        kore = self.kast_to_kore(cterm.kast)
        try:
            result = self._kore_client.get_model(kore, module_name=module_name)
        except SmtSolverError as err:
            raise self._smt_solver_error(err) from err

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
            model_subst = self.kore_to_kast(result.model)
            try:
                return Subst.from_pred(model_subst)
            except ValueError as err:
                raise AssertionError(f'Received a non-substitution from get-model endpoint: {model_subst}') from err

        else:
            raise AssertionError('Received an invalid response from get-model endpoint')

    def implies(
        self,
        antecedent: CTerm,
        consequent: CTerm,
        bind_universally: bool = False,
        failure_reason: bool = False,
        module_name: str | None = None,
        assume_defined: bool = False,
    ) -> CTermImplies:
        _LOGGER.debug(f'Checking implication: {antecedent} #Implies {consequent}')
        _consequent = consequent.kast
        unbound_consequent = [v for v in consequent.free_vars if v not in antecedent.free_vars]
        if len(unbound_consequent) > 0:
            bind_text, bind_label = ('existentially', '#Exists')
            if bind_universally:
                bind_text, bind_label = ('universally', '#Forall')
            _LOGGER.debug(f'Binding variables in consequent {bind_text}: {unbound_consequent}')
            for uc in unbound_consequent:
                # Setting Sort1 to KItem in #Exists to avoid inferring the type of each uc.
                # This should not have any effect on the resulting KORE pattern (\exists only has Sort2 as sort variable).
                _consequent = KApply(KLabel(bind_label, [K_ITEM, GENERATED_TOP_CELL]), [KVariable(uc), _consequent])
        antecedent_kore = self.kast_to_kore(antecedent.kast)
        consequent_kore = self.kast_to_kore(_consequent)
        try:
            result = self._kore_client.implies(
                antecedent_kore, consequent_kore, module_name=module_name, assume_defined=assume_defined
            )
        except SmtSolverError as err:
            raise self._smt_solver_error(err) from err

        if not result.valid:
            if result.substitution is not None:
                _LOGGER.debug(f'Received a non-empty substitution for falsifiable implication: {result.substitution}')
            if result.predicate is not None:
                _LOGGER.debug(f'Received a non-empty predicate for falsifiable implication: {result.predicate}')
            failing_cells: list[tuple[str, KInner]] = []
            remaining_implication: KInner | None = None
            if failure_reason:
                _config_match = self.implies(
                    CTerm.from_kast(antecedent.config),
                    CTerm.from_kast(consequent.config),
                    bind_universally=bind_universally,
                    failure_reason=False,
                    module_name=module_name,
                    assume_defined=assume_defined,
                )
                config_match = _config_match.csubst
                if config_match is None:
                    curr_cell_match = Subst({})
                    for cell in antecedent.cells:
                        antecedent_cell = sort_ac_collections(antecedent.cell(cell))

                        if cell not in consequent.cells:
                            failing_cells.append((cell, KRewrite(antecedent_cell, KToken('.K', sort='KItem'))))
                        else:
                            consequent_cell = sort_ac_collections(consequent.cell(cell))
                            cell_match = consequent_cell.match(antecedent_cell)
                            if cell_match is not None:
                                _curr_cell_match = curr_cell_match.union(cell_match)
                                if _curr_cell_match is not None:
                                    curr_cell_match = _curr_cell_match
                                    continue
                            failing_cells.append((cell, KRewrite(antecedent_cell, consequent_cell)))
                else:
                    consequent_constraints = list(
                        filter(
                            lambda x: not is_spurious_constraint(x),
                            map(config_match.subst, consequent.constraints),
                        )
                    )
                    remaining_implication = CTerm._ml_impl(antecedent.constraints, consequent_constraints)
            return CTermImplies(None, tuple(failing_cells), remaining_implication, result.logs)

        if result.substitution is None:
            raise ValueError('Received empty substutition for valid implication.')
        if result.predicate is None:
            raise ValueError('Received empty predicate for valid implication.')
        ml_subst = self.kore_to_kast(result.substitution)
        ml_pred = self.kore_to_kast(result.predicate)
        ml_subst_pred = mlAnd(flatten_label('#And', ml_subst) + flatten_label('#And', ml_pred))
        csubst = CSubst.from_pred(ml_subst_pred)
        return CTermImplies(csubst, (), None, result.logs)

    def assume_defined(self, cterm: CTerm, module_name: str | None = None) -> CTerm:
        _LOGGER.debug(f'Computing definedness condition for: {cterm}')
        cterm_simplified, logs = self.simplify(cterm, module_name=module_name)
        kast = KApply(KLabel('#Ceil', [GENERATED_TOP_CELL, GENERATED_TOP_CELL]), [cterm_simplified.config])
        kast_simplified, logs = self.kast_simplify(kast, module_name=module_name)
        _LOGGER.debug(f'Definedness condition computed: {kast_simplified}')
        return cterm.add_constraint(kast_simplified)

    def _smt_solver_error(self, err: SmtSolverError) -> CTermSMTError:
        kast = self.kore_to_kast(err.pattern)
        pretty_pattern = PrettyPrinter(self._definition).print(kast)
        return CTermSMTError(pretty_pattern)


@contextmanager
def cterm_symbolic(
    definition: KDefinition,
    definition_dir: Path,
    *,
    id: str | None = None,
    port: int | None = None,
    kore_rpc_command: str | Iterable[str] | None = None,
    llvm_definition_dir: Path | None = None,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    smt_tactic: str | None = None,
    bug_report: BugReport | None = None,
    haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
    haskell_log_entries: Iterable[str] = (),
    log_axioms_file: Path | None = None,
    log_succ_rewrites: bool = True,
    log_fail_rewrites: bool = False,
    start_server: bool = True,
    maude_port: int | None = None,
    fallback_on: Iterable[FallbackReason] | None = None,
    interim_simplification: int | None = None,
    no_post_exec_simplify: bool = False,
) -> Iterator[CTermSymbolic]:
    if start_server:
        # Old way of handling KoreServer, to be removed
        with kore_server(
            definition_dir=definition_dir,
            llvm_definition_dir=llvm_definition_dir,
            module_name=definition.main_module_name,
            port=port,
            command=kore_rpc_command,
            bug_report=bug_report,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            smt_tactic=smt_tactic,
            haskell_log_format=haskell_log_format,
            haskell_log_entries=haskell_log_entries,
            log_axioms_file=log_axioms_file,
            fallback_on=fallback_on,
            interim_simplification=interim_simplification,
            no_post_exec_simplify=no_post_exec_simplify,
        ) as server:
            with KoreClient('localhost', server.port, bug_report=bug_report, bug_report_id=id) as client:
                yield CTermSymbolic(
                    client, definition, log_succ_rewrites=log_succ_rewrites, log_fail_rewrites=log_fail_rewrites
                )
    else:
        if port is None:
            raise ValueError('Missing port with start_server=False')
        if maude_port is None:
            dispatch = None
        else:
            dispatch = {
                'execute': [('localhost', maude_port, TransportType.HTTP)],
                'simplify': [('localhost', maude_port, TransportType.HTTP)],
                'add-module': [
                    ('localhost', maude_port, TransportType.HTTP),
                    ('localhost', port, TransportType.SINGLE_SOCKET),
                ],
            }
        with KoreClient('localhost', port, bug_report=bug_report, bug_report_id=id, dispatch=dispatch) as client:
            yield CTermSymbolic(
                client, definition, log_succ_rewrites=log_succ_rewrites, log_fail_rewrites=log_fail_rewrites
            )
