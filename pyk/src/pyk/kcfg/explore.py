import logging
from typing import Any, ContextManager, Dict, Final, Iterable, List, Optional, Tuple

from pyk.cli_utils import BugReport
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KInner, KLabel, KVariable, Subst
from pyk.kast.manip import flatten_label, free_vars
from pyk.kore.rpc import KoreClient, KoreServer
from pyk.kore.syntax import Top
from pyk.ktool import KPrint
from pyk.prelude.k import GENERATED_TOP_CELL
from pyk.prelude.ml import is_top, mlEquals, mlTop

_LOGGER: Final = logging.getLogger(__name__)


class KCFGExplore(ContextManager['KCFGExplore']):
    kprint: KPrint
    _port: int
    _kore_server: Optional[KoreServer]
    _kore_client: Optional[KoreClient]
    _rpc_closed: bool
    _bug_report: Optional[BugReport]

    def __init__(self, kprint: KPrint, port: int, bug_report: Optional[BugReport] = None):
        self.kprint = kprint
        self._port = port
        self._bug_report = bug_report
        self._kore_server = None
        self._kore_client = None
        self._rpc_closed = False

    def __enter__(self) -> 'KCFGExplore':
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    @property
    def _kore_rpc(self) -> Tuple[KoreServer, KoreClient]:
        if self._rpc_closed:
            raise ValueError('RPC server already closed!')
        if not self._kore_server:
            self._kore_server = KoreServer(
                self.kprint.definition_dir, self.kprint.main_module, self._port, bug_report=self._bug_report
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
            _LOGGER.warning(
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
        return (Subst(_subst), ml_pred)
