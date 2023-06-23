from __future__ import annotations

import json
import logging
from itertools import chain
from typing import TYPE_CHECKING

from pyk.kore.rpc import LogEntry

from ..kast.inner import KRewrite, KSort
from ..kast.manip import flatten_label, ml_pred_to_bool
from ..kast.outer import KClaim
from ..kcfg import KCFG
from ..prelude.ml import mlAnd, mlTop
from ..utils import hash_str, shorten_hashes
from .proof import Proof, ProofStatus

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final, TypeVar

    from ..cterm import CTerm
    from ..kast.inner import KInner
    from ..kast.outer import KDefinition
    from ..kcfg import KCFGExplore
    from ..kcfg.kcfg import NodeIdLike
    from ..ktool.kprint import KPrint

    T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


class APRProof(Proof):
    """APRProof and APRProver implement all-path reachability logic,
    as introduced by A. Stefanescu and others in their paper 'All-Path Reachability Logic':
    https://doi.org/10.23638/LMCS-15(2:5)2019
    Note that reachability logic formula `phi =>A psi` has *not* the same meaning
    as CTL/CTL*'s `phi -> AF psi`, since reachability logic ignores infinite traces.
    """

    kcfg: KCFG
    init: NodeIdLike
    target: NodeIdLike
    _terminal_nodes: list[NodeIdLike]
    logs: dict[int, tuple[LogEntry, ...]]
    circularity: bool

    def __init__(
        self,
        id: str,
        kcfg: KCFG,
        init: NodeIdLike,
        target: NodeIdLike,
        logs: dict[int, tuple[LogEntry, ...]],
        terminal_nodes: Iterable[NodeIdLike] | None = None,
        proof_dir: Path | None = None,
        subproof_ids: Iterable[str] = (),
        circularity: bool = False,
        admitted: bool = False,
    ):
        super().__init__(id, proof_dir=proof_dir, subproof_ids=subproof_ids, admitted=admitted)
        self.kcfg = kcfg
        self.init = init
        self.target = target
        self.logs = logs
        self.circularity = circularity
        self._terminal_nodes = list(terminal_nodes) if terminal_nodes is not None else []

    @property
    def terminal(self) -> list[KCFG.Node]:
        return [self.kcfg.node(nid) for nid in self._terminal_nodes]

    @property
    def pending(self) -> list[KCFG.Node]:
        return [nd for nd in self.kcfg.leaves if self.is_pending(nd.id)]

    @property
    def failing(self) -> list[KCFG.Node]:
        return [nd for nd in self.kcfg.leaves if self.is_failing(nd.id)]

    def is_terminal(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) in (self.kcfg._resolve(nid) for nid in self._terminal_nodes)

    def is_pending(self, node_id: NodeIdLike) -> bool:
        return self.kcfg.is_leaf(node_id) and not (
            self.is_terminal(node_id) or self.kcfg.is_stuck(node_id) or self.is_target(node_id)
        )

    def is_init(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) == self.kcfg._resolve(self.init)

    def is_target(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) == self.kcfg._resolve(self.target)

    def is_failing(self, node_id: NodeIdLike) -> bool:
        return self.kcfg.is_leaf(node_id) and not (self.is_pending(node_id) or self.is_target(node_id))

    @staticmethod
    def read_proof(id: str, proof_dir: Path) -> APRProof:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        if APRProof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            _LOGGER.info(f'Reading APRProof from file {id}: {proof_path}')
            return APRProof.from_dict(proof_dict, proof_dir=proof_dir)
        raise ValueError(f'Could not load APRProof from file {id}: {proof_path}')

    @property
    def status(self) -> ProofStatus:
        if self.admitted:
            return ProofStatus.PASSED
        if len(self.failing) > 0 or self.subproofs_status == ProofStatus.FAILED:
            return ProofStatus.FAILED
        elif len(self.pending) > 0 or self.subproofs_status == ProofStatus.PENDING:
            return ProofStatus.PENDING
        else:
            return ProofStatus.PASSED

    @classmethod
    def from_dict(cls: type[APRProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> APRProof:
        cfg = KCFG.from_dict(dct['cfg'])
        init_node = dct['init']
        terminal_nodes = dct['terminal_nodes']
        target_node = dct['target']
        id = dct['id']
        circularity = dct.get('circularity', False)
        admitted = dct.get('admitted', False)
        subproof_ids = dct['subproof_ids'] if 'subproof_ids' in dct else []
        if 'logs' in dct:
            logs = {k: tuple(LogEntry.from_dict(l) for l in ls) for k, ls in dct['logs'].items()}
        else:
            logs = {}

        return APRProof(
            id,
            cfg,
            init_node,
            target_node,
            logs=logs,
            terminal_nodes=terminal_nodes,
            circularity=circularity,
            admitted=admitted,
            proof_dir=proof_dir,
            subproof_ids=subproof_ids,
        )

    @staticmethod
    def from_claim(
        defn: KDefinition, claim: KClaim, logs: dict[int, tuple[LogEntry, ...]], *args: Any, **kwargs: Any
    ) -> APRProof:
        cfg, init_node, target_node = KCFG.from_claim(defn, claim)
        return APRProof(claim.label, cfg, init=init_node, target=target_node, logs=logs, **kwargs)

    def as_claim(self, kprint: KPrint) -> KClaim:
        fr: CTerm = self.kcfg.node(self.init).cterm
        to: CTerm = self.kcfg.node(self.target).cterm
        fr_config_sorted = kprint.definition.sort_vars(fr.config, sort=KSort('GeneratedTopCell'))
        to_config_sorted = kprint.definition.sort_vars(to.config, sort=KSort('GeneratedTopCell'))
        kc = KClaim(
            body=KRewrite(fr_config_sorted, to_config_sorted),
            requires=ml_pred_to_bool(mlAnd(fr.constraints)),
            ensures=ml_pred_to_bool(mlAnd(to.constraints)),
        )
        return kc

    def path_constraints(self, final_node_id: NodeIdLike) -> KInner:
        path = self.kcfg.shortest_path_between(self.init, final_node_id)
        if path is None:
            raise ValueError(f'No path found to specified node: {final_node_id}')
        curr_constraint: KInner = mlTop()
        for edge in reversed(path):
            if type(edge) is KCFG.Split:
                assert len(edge.targets) == 1
                csubst = edge.splits[edge.targets[0].id]
                curr_constraint = mlAnd([csubst.subst.ml_pred, csubst.constraint, curr_constraint])
            if type(edge) is KCFG.Cover:
                curr_constraint = mlAnd([edge.csubst.constraint, edge.csubst.subst.apply(curr_constraint)])
        return mlAnd(flatten_label('#And', curr_constraint))

    @property
    def dict(self) -> dict[str, Any]:
        dct = super().dict
        dct['type'] = 'APRProof'
        dct['cfg'] = self.kcfg.to_dict()
        dct['init'] = self.init
        dct['target'] = self.target
        dct['terminal_nodes'] = self._terminal_nodes
        dct['circularity'] = self.circularity
        logs = {k: [l.to_dict() for l in ls] for k, ls in self.logs.items()}
        dct['logs'] = logs
        return dct

    def add_terminal(self, nid: NodeIdLike) -> None:
        self._terminal_nodes.append(self.kcfg._resolve(nid))

    @property
    def summary(self) -> Iterable[str]:
        subproofs_summaries = chain(subproof.summary for subproof in self.subproofs)
        yield from [
            f'APRProof: {self.id}',
            f'    status: {self.status}',
            f'    admitted: {self.admitted}',
            f'    nodes: {len(self.kcfg.nodes)}',
            f'    pending: {len(self.pending)}',
            f'    failing: {len(self.failing)}',
            f'    stuck: {len(self.kcfg.stuck)}',
            f'    terminal: {len(self.terminal)}',
            f'Subproofs: {len(self.subproof_ids)}',
        ]
        for summary in subproofs_summaries:
            yield from summary


class APRBMCProof(APRProof):
    """APRBMCProof and APRBMCProver perform bounded model-checking of an all-path reachability logic claim."""

    bmc_depth: int
    _bounded_nodes: list[NodeIdLike]

    def __init__(
        self,
        id: str,
        kcfg: KCFG,
        init: NodeIdLike,
        target: NodeIdLike,
        logs: dict[int, tuple[LogEntry, ...]],
        bmc_depth: int,
        bounded_nodes: Iterable[int] | None = None,
        proof_dir: Path | None = None,
        subproof_ids: Iterable[str] = (),
        circularity: bool = False,
        admitted: bool = False,
    ):
        super().__init__(
            id,
            kcfg,
            init,
            target,
            logs,
            proof_dir=proof_dir,
            subproof_ids=subproof_ids,
            circularity=circularity,
            admitted=admitted,
        )
        self.bmc_depth = bmc_depth
        self._bounded_nodes = list(bounded_nodes) if bounded_nodes is not None else []

    @staticmethod
    def read_proof(id: str, proof_dir: Path) -> APRBMCProof:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        if APRBMCProof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            _LOGGER.info(f'Reading APRBMCProof from file {id}: {proof_path}')
            return APRBMCProof.from_dict(proof_dict, proof_dir=proof_dir)
        raise ValueError(f'Could not load APRBMCProof from file {id}: {proof_path}')

    @property
    def bounded(self) -> list[KCFG.Node]:
        return [nd for nd in self.kcfg.leaves if self.is_bounded(nd.id)]

    def is_bounded(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) in (self.kcfg._resolve(nid) for nid in self._bounded_nodes)

    def is_failing(self, node_id: NodeIdLike) -> bool:
        return self.kcfg.is_leaf(node_id) and not (
            self.is_pending(node_id) or self.is_target(node_id) or self.is_bounded(node_id)
        )

    def is_pending(self, node_id: NodeIdLike) -> bool:
        return self.kcfg.is_leaf(node_id) and not (
            self.is_terminal(node_id)
            or self.kcfg.is_stuck(node_id)
            or self.is_bounded(node_id)
            or self.is_target(node_id)
        )

    @classmethod
    def from_dict(cls: type[APRBMCProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> APRBMCProof:
        cfg = KCFG.from_dict(dct['cfg'])
        init = dct['init']
        target = dct['target']
        bounded_nodes = dct['bounded_nodes']

        admitted = dct.get('admitted', False)
        circularity = dct.get('circularity', False)
        bmc_depth = dct['bmc_depth']
        id = dct['id']
        subproof_ids = dct['subproof_ids'] if 'subproof_ids' in dct else []
        if 'logs' in dct:
            logs = {k: tuple(LogEntry.from_dict(l) for l in ls) for k, ls in dct['logs'].items()}
        else:
            logs = {}

        return APRBMCProof(
            id,
            cfg,
            init,
            target,
            logs,
            bmc_depth,
            bounded_nodes=bounded_nodes,
            proof_dir=proof_dir,
            circularity=circularity,
            subproof_ids=subproof_ids,
            admitted=admitted,
        )

    @staticmethod
    def from_claim_with_bmc_depth(defn: KDefinition, claim: KClaim, bmc_depth: int) -> APRBMCProof:
        cfg, init_node, target_node = KCFG.from_claim(defn, claim)
        return APRBMCProof(claim.label, cfg, init_node, target_node, {}, bmc_depth)

    @property
    def dict(self) -> dict[str, Any]:
        logs = {k: [l.to_dict() for l in ls] for k, ls in self.logs.items()}
        dct = super().dict
        dct['type'] = 'APRBMCProof'
        dct['bmc_depth'] = self.bmc_depth
        dct['bounded_nodes'] = self._bounded_nodes
        dct['logs'] = logs
        dct['circularity'] = self.circularity
        return dct

    def add_bounded(self, nid: NodeIdLike) -> None:
        self._bounded_nodes.append(self.kcfg._resolve(nid))

    @property
    def summary(self) -> Iterable[str]:
        subproofs_summaries = chain(subproof.summary for subproof in self.subproofs)
        yield from [
            f'APRBMCProof(depth={self.bmc_depth}): {self.id}',
            f'    status: {self.status}',
            f'    nodes: {len(self.kcfg.nodes)}',
            f'    pending: {len(self.pending)}',
            f'    failing: {len(self.failing)}',
            f'    stuck: {len(self.kcfg.stuck)}',
            f'    terminal: {len(self.terminal)}',
            f'    bounded: {len(self.bounded)}',
            f'Subproofs: {len(self.subproof_ids)}',
        ]
        for summary in subproofs_summaries:
            yield from summary


class APRProver:
    proof: APRProof
    kcfg_explore: KCFGExplore
    _is_terminal: Callable[[CTerm], bool] | None
    _extract_branches: Callable[[CTerm], Iterable[KInner]] | None
    _abstract_node: Callable[[CTerm], CTerm] | None

    main_module_name: str
    dependencies_module_name: str
    circularities_module_name: str

    def __init__(
        self,
        proof: APRProof,
        kcfg_explore: KCFGExplore,
        is_terminal: Callable[[CTerm], bool] | None = None,
        extract_branches: Callable[[CTerm], Iterable[KInner]] | None = None,
        abstract_node: Callable[[CTerm], CTerm] | None = None,
    ) -> None:
        self.proof = proof
        self.kcfg_explore = kcfg_explore
        self._is_terminal = is_terminal
        self._extract_branches = extract_branches
        self._abstract_node = abstract_node
        self.main_module_name = self.kcfg_explore.kprint.definition.main_module_name

        subproofs: list[Proof] = (
            [Proof.read_proof(i, proof_dir=proof.proof_dir) for i in proof.subproof_ids]
            if proof.proof_dir is not None
            else []
        )

        apr_subproofs: list[APRProof] = [pf for pf in subproofs if isinstance(pf, APRProof)]

        dependencies_as_claims: list[KClaim] = [d.as_claim(self.kcfg_explore.kprint) for d in apr_subproofs]

        self.dependencies_module_name = self.main_module_name + '-DEPENDS-MODULE'
        self.kcfg_explore.add_dependencies_module(
            self.main_module_name,
            self.dependencies_module_name,
            dependencies_as_claims,
            priority=1,
        )
        self.circularities_module_name = self.main_module_name + '-CIRCULARITIES-MODULE'
        self.kcfg_explore.add_dependencies_module(
            self.main_module_name,
            self.circularities_module_name,
            dependencies_as_claims + ([proof.as_claim(self.kcfg_explore.kprint)] if proof.circularity else []),
            priority=1,
        )

    def _check_terminal(self, curr_node: KCFG.Node) -> bool:
        if self._is_terminal is not None:
            _LOGGER.info(f'Checking terminal {self.proof.id}: {shorten_hashes(curr_node.id)}')
            if self._is_terminal(curr_node.cterm):
                _LOGGER.info(f'Terminal node {self.proof.id}: {shorten_hashes(curr_node.id)}.')
                self.proof.add_terminal(curr_node.id)
                return True
        return False

    def nonzero_depth(self, node: KCFG.Node) -> bool:
        init = self.proof.kcfg.node(self.proof.init)
        p = self.proof.kcfg.shortest_path_between(init.id, node.id)
        if p is None:
            return False
        return KCFG.path_length(p) > 0

    def _check_subsume(self, node: KCFG.Node) -> bool:
        target_node = self.proof.kcfg.node(self.proof.target)
        _LOGGER.info(
            f'Checking subsumption into target state {self.proof.id}: {shorten_hashes((node.id, target_node.id))}'
        )
        csubst = self.kcfg_explore.cterm_implies(node.cterm, target_node.cterm)
        if csubst is not None:
            self.proof.kcfg.create_cover(node.id, target_node.id, csubst=csubst)
            _LOGGER.info(f'Subsumed into target node {self.proof.id}: {shorten_hashes((node.id, target_node.id))}')
            return True
        return False

    def _check_abstract(self, node: KCFG.Node) -> bool:
        if self._abstract_node is None:
            return False

        new_cterm = self._abstract_node(node.cterm)
        if new_cterm == node.cterm:
            return False

        new_node = self.proof.kcfg.create_node(new_cterm)
        self.proof.kcfg.create_cover(node.id, new_node.id)
        return True

    def advance_proof(
        self,
        max_iterations: int | None = None,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        implication_every_block: bool = True,
    ) -> KCFG:
        iterations = 0

        while self.proof.pending:
            self.proof.write_proof()

            if max_iterations is not None and max_iterations <= iterations:
                _LOGGER.warning(f'Reached iteration bound {self.proof.id}: {max_iterations}')
                break
            iterations += 1
            curr_node = self.proof.pending[0]

            if self._check_subsume(curr_node):
                continue

            if self._check_terminal(curr_node):
                continue

            if self._check_abstract(curr_node):
                continue

            if self._extract_branches is not None and len(self.proof.kcfg.splits(target_id=curr_node.id)) == 0:
                branches = list(self._extract_branches(curr_node.cterm))
                if len(branches) > 0:
                    self.proof.kcfg.split_on_constraints(curr_node.id, branches)
                    _LOGGER.info(
                        f'Found {len(branches)} branches using heuristic for node {self.proof.id}: {shorten_hashes(curr_node.id)}: {[self.kcfg_explore.kprint.pretty_print(bc) for bc in branches]}'
                    )
                    continue

            module_name = (
                self.circularities_module_name if self.nonzero_depth(curr_node) else self.dependencies_module_name
            )
            self.kcfg_explore.extend(
                self.proof.kcfg,
                curr_node,
                self.proof.logs,
                execute_depth=execute_depth,
                cut_point_rules=cut_point_rules,
                terminal_rules=terminal_rules,
                module_name=module_name,
            )

        self.proof.write_proof()
        return self.proof.kcfg


class APRBMCProver(APRProver):
    proof: APRBMCProof
    _same_loop: Callable[[CTerm, CTerm], bool]
    _checked_nodes: list[int]

    def __init__(
        self,
        proof: APRBMCProof,
        kcfg_explore: KCFGExplore,
        same_loop: Callable[[CTerm, CTerm], bool],
        is_terminal: Callable[[CTerm], bool] | None = None,
        extract_branches: Callable[[CTerm], Iterable[KInner]] | None = None,
        abstract_node: Callable[[CTerm], CTerm] | None = None,
    ) -> None:
        super().__init__(
            proof,
            kcfg_explore=kcfg_explore,
            is_terminal=is_terminal,
            extract_branches=extract_branches,
            abstract_node=abstract_node,
        )
        self._same_loop = same_loop
        self._checked_nodes = []

    def advance_proof(
        self,
        max_iterations: int | None = None,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        implication_every_block: bool = True,
    ) -> KCFG:
        iterations = 0

        while self.proof.pending:
            self.proof.write_proof()

            if max_iterations is not None and max_iterations <= iterations:
                _LOGGER.warning(f'Reached iteration bound {self.proof.id}: {max_iterations}')
                break
            iterations += 1

            for f in self.proof.pending:
                if f.id not in self._checked_nodes:
                    self._checked_nodes.append(f.id)
                    prior_loops = [
                        nd.id
                        for nd in self.proof.kcfg.reachable_nodes(f.id, reverse=True)
                        if nd.id != f.id and self._same_loop(nd.cterm, f.cterm)
                    ]
                    if len(prior_loops) >= self.proof.bmc_depth:
                        self.proof.add_bounded(f.id)

            super().advance_proof(
                max_iterations=1,
                execute_depth=execute_depth,
                cut_point_rules=cut_point_rules,
                terminal_rules=terminal_rules,
                implication_every_block=implication_every_block,
            )

        self.proof.write_proof()
        return self.proof.kcfg
