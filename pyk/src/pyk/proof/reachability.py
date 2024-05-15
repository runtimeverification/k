from __future__ import annotations

import graphlib
import json
import logging
import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from pyk.kore.rpc import LogEntry

from ..cterm.cterm import remove_useless_constraints
from ..kast.inner import KInner, Subst
from ..kast.manip import flatten_label, free_vars, ml_pred_to_bool
from ..kast.outer import KFlatModule, KImport, KRule
from ..kcfg import KCFG, KCFGStore
from ..kcfg.exploration import KCFGExploration
from ..konvert import kflatmodule_to_kore
from ..prelude.ml import mlAnd, mlTop
from ..utils import FrozenDict, ensure_dir_path, hash_str, shorten_hashes, single
from .implies import ProofSummary, Prover, RefutationProof
from .proof import CompositeSummary, FailureInfo, Proof, ProofStatus

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final, TypeVar

    from ..kast.outer import KClaim, KDefinition, KFlatModuleList, KRuleLike
    from ..kcfg import KCFGExplore
    from ..kcfg.explore import KCFGExtendResult
    from ..kcfg.kcfg import CSubst, NodeIdLike

    T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


@dataclass
class APRProofResult:
    node_id: int
    prior_loops_cache_update: tuple[int, ...]


@dataclass
class APRProofExtendResult(APRProofResult):
    extend_result: KCFGExtendResult


@dataclass
class APRProofSubsumeResult(APRProofResult):
    csubst: CSubst


@dataclass
class APRProofTerminalResult(APRProofResult): ...


@dataclass
class APRProofBoundedResult(APRProofResult): ...


@dataclass(frozen=True)
class APRProofStep:
    node: KCFG.Node
    target: KCFG.Node
    proof_id: str
    bmc_depth: int | None
    module_name: str
    shortest_path_to_node: tuple[KCFG.Node, ...]
    prior_loops_cache: FrozenDict[int, tuple[int, ...]] = field(compare=False)


class APRProof(Proof[APRProofStep, APRProofResult], KCFGExploration):
    """APRProof and APRProver implement all-path reachability logic,
    as introduced by A. Stefanescu and others in their paper 'All-Path Reachability Logic':
    https://doi.org/10.23638/LMCS-15(2:5)2019
    Note that reachability logic formula `phi =>A psi` has *not* the same meaning
    as CTL/CTL*'s `phi -> AF psi`, since reachability logic ignores infinite traces.
    This implementation extends the above with bounded model checking, allowing the user
    to specify an optional loop iteration bound for each loop in execution.
    """

    node_refutations: dict[int, RefutationProof]  # TODO _node_refutatations
    init: int
    target: int
    bmc_depth: int | None
    _bounded: set[int]
    logs: dict[int, tuple[LogEntry, ...]]
    circularity: bool
    _exec_time: float
    error_info: Exception | None
    prior_loops_cache: dict[int, tuple[int, ...]]

    _checked_for_bounded: set[int]

    def __init__(
        self,
        id: str,
        kcfg: KCFG,
        terminal: Iterable[int],
        init: NodeIdLike,
        target: NodeIdLike,
        logs: dict[int, tuple[LogEntry, ...]],
        bmc_depth: int | None = None,
        bounded: Iterable[int] | None = None,
        proof_dir: Path | None = None,
        node_refutations: dict[int, str] | None = None,
        subproof_ids: Iterable[str] = (),
        circularity: bool = False,
        admitted: bool = False,
        _exec_time: float = 0,
        error_info: Exception | None = None,
        prior_loops_cache: dict[int, tuple[int, ...]] | None = None,
    ):
        Proof.__init__(self, id, proof_dir=proof_dir, subproof_ids=subproof_ids, admitted=admitted)
        KCFGExploration.__init__(self, kcfg, terminal)

        self.failure_info = None
        self.init = kcfg._resolve(init)
        self.target = kcfg._resolve(target)
        self.bmc_depth = bmc_depth
        self._bounded = set(bounded) if bounded is not None else set()
        self.logs = logs
        self.circularity = circularity
        self.node_refutations = {}
        self.prior_loops_cache = prior_loops_cache if prior_loops_cache is not None else {}
        self.kcfg._kcfg_store = KCFGStore(self.proof_subdir / 'kcfg') if self.proof_subdir else None
        self._exec_time = _exec_time
        self.error_info = error_info

        self._checked_for_bounded = set()

        if self.proof_dir is not None and self.proof_subdir is not None:
            ensure_dir_path(self.proof_dir)
            ensure_dir_path(self.proof_subdir)

        if node_refutations is not None:
            refutations_not_in_subprroofs = set(node_refutations.values()).difference(
                set(subproof_ids if subproof_ids else [])
            )
            if refutations_not_in_subprroofs:
                raise ValueError(
                    f'All node refutations must be included in subproofs, violators are {refutations_not_in_subprroofs}'
                )
            for node_id, proof_id in node_refutations.items():
                subproof = self._subproofs[proof_id]
                assert type(subproof) is RefutationProof
                self.node_refutations[node_id] = subproof

    def get_steps(self) -> list[APRProofStep]:
        steps: list[APRProofStep] = []
        for node in self.pending:

            shortest_path: list[KCFG.Node] = []
            if self.bmc_depth is not None:
                shortest_path = []
                for succ in reversed(self.shortest_path_to(node.id)):
                    if self.kcfg.zero_depth_between(succ.source.id, node.id):
                        ...
                    else:
                        shortest_path.append(succ.source)

            def nonzero_depth(proof: APRProof, node: KCFG.Node) -> bool:
                return not proof.kcfg.zero_depth_between(proof.init, node.id)

            module_name = self.circularities_module_name if nonzero_depth(self, node) else self.dependencies_module_name

            steps.append(
                APRProofStep(
                    bmc_depth=self.bmc_depth,
                    module_name=module_name,
                    node=node,
                    proof_id=self.id,
                    target=self.kcfg.node(self.target),
                    shortest_path_to_node=tuple(shortest_path),
                    prior_loops_cache=FrozenDict(self.prior_loops_cache),
                )
            )
        return steps

    def commit(self, result: APRProofResult) -> None:
        self.prior_loops_cache[result.node_id] = result.prior_loops_cache_update
        if isinstance(result, APRProofExtendResult):
            self.kcfg.extend(result.extend_result, self.kcfg.node(result.node_id), logs=self.logs)
        elif isinstance(result, APRProofSubsumeResult):
            self.kcfg.create_cover(result.node_id, self.target, csubst=result.csubst)
        elif isinstance(result, APRProofTerminalResult):
            self.add_terminal(result.node_id)
        elif isinstance(result, APRProofBoundedResult):
            self.add_bounded(result.node_id)
        else:
            raise ValueError(f'Incorrect result type, expected APRProofResult: {result}')

    @property
    def module_name(self) -> str:
        return self._make_module_name(self.id)

    @property
    def pending(self) -> list[KCFG.Node]:
        return [node for node in self.explorable if self.is_pending(node.id)]

    @property
    def failing(self) -> list[KCFG.Node]:
        return [nd for nd in self.kcfg.leaves if self.is_failing(nd.id)]

    @property
    def bounded(self) -> list[KCFG.Node]:
        return [nd for nd in self.kcfg.leaves if self.is_bounded(nd.id)]

    def is_refuted(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) in self.node_refutations.keys()

    def is_pending(self, node_id: NodeIdLike) -> bool:
        return (
            self.is_explorable(node_id)
            and not self.is_target(node_id)
            and not self.is_refuted(node_id)
            and not self.is_bounded(node_id)
        )

    @property
    def circularities_module_name(self) -> str:
        return self.module_name + '-CIRCULARITIES-MODULE'

    @property
    def dependencies_module_name(self) -> str:
        return self.module_name + '-DEPENDS-MODULE'

    def is_init(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) == self.kcfg._resolve(self.init)

    def is_target(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) == self.kcfg._resolve(self.target)

    def is_failing(self, node_id: NodeIdLike) -> bool:
        return (
            self.kcfg.is_leaf(node_id)
            and not self.is_explorable(node_id)
            and not self.is_target(node_id)
            and not self.is_refuted(node_id)
            and not self.kcfg.is_vacuous(node_id)
            and not self.is_bounded(node_id)
        )

    def is_bounded(self, node_id: NodeIdLike) -> bool:
        return self.kcfg._resolve(node_id) in self._bounded

    def add_bounded(self, nid: NodeIdLike) -> None:
        self._bounded.add(self.kcfg._resolve(nid))

    def shortest_path_to(self, node_id: NodeIdLike) -> tuple[KCFG.Successor, ...]:
        spb = self.kcfg.shortest_path_between(self.init, node_id)
        assert spb is not None
        return spb

    def prune(self, node_id: NodeIdLike, keep_nodes: Iterable[NodeIdLike] = ()) -> list[int]:
        pruned_nodes = super().prune(node_id, keep_nodes=list(keep_nodes) + [self.init, self.target])
        for nid in pruned_nodes:
            self._bounded.discard(nid)
            self.prior_loops_cache = {k: v for (k, v) in self.prior_loops_cache.items() if k != nid}
            for k, v in self.prior_loops_cache.items():
                if nid in v:
                    self.prior_loops_cache[k] = tuple(_nid for _nid in self.prior_loops_cache[k] if _nid != nid)

        return pruned_nodes

    @property
    def exec_time(self) -> float:
        return self._exec_time

    def add_exec_time(self, exec_time: float) -> None:
        self._exec_time += exec_time

    def set_exec_time(self, exec_time: float) -> None:
        self._exec_time = exec_time

    def formatted_exec_time(self) -> str:
        exec_time = round(self.exec_time)
        h, remainder = divmod(exec_time, 3600)
        m, s = divmod(remainder, 60)
        formatted = []
        if h:
            formatted.append(f'{h}h')
        if m or h:
            formatted.append(f'{m}m')
        formatted.append(f'{s}s')
        return ' '.join(formatted)

    @staticmethod
    def _make_module_name(proof_id: str) -> str:
        return 'M-' + re.sub(
            r'[\[\]]|[_%().:,]+', lambda match: 'bkt' if match.group(0) in ['[', ']'] else '-', proof_id.upper()
        )

    @staticmethod
    def read_proof(id: str, proof_dir: Path) -> APRProof:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        if APRProof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            _LOGGER.info(f'Reading APRProof from file {id}: {proof_path}')
            return APRProof.from_dict(proof_dict, proof_dir=proof_dir)
        raise ValueError(f'Could not load APRProof from file {id}: {proof_path}')

    @property
    def own_status(self) -> ProofStatus:
        if self.admitted:
            return ProofStatus.PASSED
        if len(self.failing) > 0:
            return ProofStatus.FAILED
        if len(self.pending) > 0:
            return ProofStatus.PENDING
        return ProofStatus.PASSED

    @property
    def can_progress(self) -> bool:
        return len(self.pending) > 0

    @classmethod
    def from_dict(cls: type[APRProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> APRProof:
        kcfg = KCFG.from_dict(dct['kcfg'])
        terminal = dct['terminal']
        init_node = dct['init']
        target_node = dct['target']
        id = dct['id']
        circularity = dct.get('circularity', False)
        admitted = dct.get('admitted', False)
        subproof_ids = dct['subproof_ids'] if 'subproof_ids' in dct else []
        node_refutations: dict[int, str] = {}
        if 'node_refutation' in dct:
            node_refutations = {
                kcfg._resolve(int(node_id)): proof_id for node_id, proof_id in dct['node_refutations'].items()
            }
        if 'logs' in dct:
            logs = {int(k): tuple(LogEntry.from_dict(l) for l in ls) for k, ls in dct['logs'].items()}
        else:
            logs = {}

        bounded = dct['bounded']
        bmc_depth = dct['bmc_depth'] if 'bmc_depth' in dct else None

        return APRProof(
            id,
            kcfg,
            terminal,
            init_node,
            target_node,
            logs=logs,
            bmc_depth=bmc_depth,
            bounded=bounded,
            circularity=circularity,
            admitted=admitted,
            proof_dir=proof_dir,
            subproof_ids=subproof_ids,
            node_refutations=node_refutations,
        )

    @staticmethod
    def from_claim(
        defn: KDefinition,
        claim: KClaim,
        logs: dict[int, tuple[LogEntry, ...]],
        proof_dir: Path | None = None,
        bmc_depth: int | None = None,
        **kwargs: Any,
    ) -> APRProof:
        kcfg_dir = proof_dir / claim.label / 'kcfg' if proof_dir is not None else None

        kcfg, init_node, target_node = KCFG.from_claim(defn, claim, cfg_dir=kcfg_dir)
        return APRProof(
            claim.label,
            kcfg,
            [],
            init=init_node,
            target=target_node,
            logs=logs,
            bmc_depth=bmc_depth,
            proof_dir=proof_dir,
            circularity=claim.is_circularity,
            admitted=claim.is_trusted,
            **kwargs,
        )

    def as_rule(self, priority: int = 20) -> KRule:
        _edge = KCFG.Edge(self.kcfg.node(self.init), self.kcfg.node(self.target), depth=0, rules=())
        _rule = _edge.to_rule('BASIC-BLOCK', priority=priority)
        assert type(_rule) is KRule
        return _rule

    @staticmethod
    def from_spec_modules(
        defn: KDefinition,
        spec_modules: KFlatModuleList,
        logs: dict[int, tuple[LogEntry, ...]],
        proof_dir: Path | None = None,
        spec_labels: Iterable[str] | None = None,
        **kwargs: Any,
    ) -> list[APRProof]:
        claims_by_label = {claim.label: claim for module in spec_modules.modules for claim in module.claims}
        if spec_labels is None:
            spec_labels = list(claims_by_label.keys())
        _spec_labels = []
        for spec_label in spec_labels:
            if spec_label in claims_by_label:
                _spec_labels.append(spec_label)
            elif f'{spec_modules.main_module}.{spec_label}' in claims_by_label:
                _spec_labels.append(f'{spec_modules.main_module}.{spec_label}')
            else:
                raise ValueError(
                    f'Could not find specification label: {spec_label} or {spec_modules.main_module}.{spec_label}'
                )
        spec_labels = _spec_labels

        claims_graph: dict[str, list[str]] = {}
        unfound_dependencies = []
        for module in spec_modules.modules:
            for claim in module.claims:
                claims_graph[claim.label] = []
                for dependency in claim.dependencies:
                    if dependency in claims_by_label:
                        claims_graph[claim.label].append(dependency)
                    elif f'{module.name}.{dependency}' in claims_by_label:
                        claims_graph[claim.label].append(f'{module.name}.{dependency}')
                    else:
                        unfound_dependencies.append((claim.label, module.name, dependency))
        if unfound_dependencies:
            unfound_dependency_list = [
                f'Could not find dependency for claim {label}: {dependency} or {module_name}.{dependency}'
                for label, module_name, dependency in unfound_dependencies
            ]
            unfound_dependency_message = '\n - ' + '\n - '.join(unfound_dependency_list)
            raise ValueError(f'Could not find dependencies:{unfound_dependency_message}')

        claims_subgraph: dict[str, list[str]] = {}
        remaining_claims = spec_labels
        while len(remaining_claims) > 0:
            claim_label = remaining_claims.pop()
            claims_subgraph[claim_label] = claims_graph[claim_label]
            remaining_claims.extend(claims_graph[claim_label])

        topological_sorter = graphlib.TopologicalSorter(claims_subgraph)
        topological_sorter.prepare()
        apr_proofs: list[APRProof] = []
        while topological_sorter.is_active():
            for claim_label in topological_sorter.get_ready():
                if proof_dir is not None and Proof.proof_data_exists(claim_label, proof_dir):
                    apr_proof = APRProof.read_proof_data(proof_dir, claim_label)
                else:
                    _LOGGER.info(f'Building APRProof for claim: {claim_label}')
                    claim = claims_by_label[claim_label]
                    apr_proof = APRProof.from_claim(
                        defn,
                        claim,
                        logs=logs,
                        proof_dir=proof_dir,
                        subproof_ids=claims_graph[claim_label],
                    )
                    apr_proof.write_proof_data()
                apr_proofs.append(apr_proof)
                topological_sorter.done(claim_label)

        return apr_proofs

    def path_constraints(self, final_node_id: NodeIdLike) -> KInner:
        path = self.shortest_path_to(final_node_id)
        curr_constraint: KInner = mlTop()
        for edge in reversed(path):
            if type(edge) is KCFG.Split:
                assert len(edge.targets) == 1
                csubst = edge.splits[edge.targets[0].id]
                curr_constraint = mlAnd([csubst.subst.minimize().ml_pred, csubst.constraint, curr_constraint])
            if type(edge) is KCFG.Cover:
                curr_constraint = mlAnd([edge.csubst.constraint, edge.csubst.subst.apply(curr_constraint)])
        return mlAnd(flatten_label('#And', curr_constraint))

    @property
    def dict(self) -> dict[str, Any]:
        # Note: We are relying on the order of inheritance to
        # access `dict` of `Proof`, since mypy is having issues
        # with the two correct solutions.
        dct = super().dict
        dct['type'] = 'APRProof'
        dct['kcfg'] = self.kcfg.to_dict()
        dct['terminal'] = sorted(node.id for node in self.kcfg.nodes if self.is_terminal(node.id))
        dct['init'] = self.init
        dct['target'] = self.target
        dct['bounded'] = list(self._bounded)
        if self.bmc_depth is not None:
            dct['bmc_depth'] = self.bmc_depth
        dct['node_refutations'] = {node_id: proof.id for (node_id, proof) in self.node_refutations.items()}
        dct['circularity'] = self.circularity
        logs = {int(k): [l.to_dict() for l in ls] for k, ls in self.logs.items()}
        dct['logs'] = logs
        return dct

    @property
    def summary(self) -> CompositeSummary:
        subproofs_summaries = [subproof.summary for subproof in self.subproofs]
        return CompositeSummary(
            [
                APRSummary(
                    self.id,
                    self.status,
                    self.admitted,
                    len(self.kcfg.nodes),
                    len(self.pending),
                    len(self.failing),
                    len(self.kcfg.vacuous),
                    len(self.kcfg.stuck),
                    len([node for node in self.kcfg.nodes if self.is_terminal(node.id)]),
                    len(self.node_refutations),
                    self.bmc_depth,
                    len(self._bounded),
                    len(self.subproof_ids),
                    self.formatted_exec_time(),
                ),
                *subproofs_summaries,
            ]
        )

    def get_refutation_id(self, node_id: int) -> str:
        return f'{self.id}.node-infeasible-{node_id}'

    @staticmethod
    def read_proof_data(proof_dir: Path, id: str) -> APRProof:
        proof_subdir = proof_dir / id
        proof_json = proof_subdir / 'proof.json'
        proof_dict = json.loads(proof_json.read_text())
        cfg_dir = proof_subdir / 'kcfg'
        kcfg = KCFG.read_cfg_data(cfg_dir)
        init = int(proof_dict['init'])
        target = int(proof_dict['target'])
        bounded = proof_dict['bounded']
        bmc_depth = int(proof_dict['bmc_depth']) if 'bmc_depth' in proof_dict else None
        circularity = bool(proof_dict['circularity'])
        admitted = bool(proof_dict['admitted'])
        exec_time = float(proof_dict['execution_time']) if 'execution_time' in proof_dict else 0.0
        terminal = proof_dict['terminal']
        logs = {int(k): tuple(LogEntry.from_dict(l) for l in ls) for k, ls in proof_dict['logs'].items()}
        subproof_ids = proof_dict['subproof_ids']
        node_refutations = {
            kcfg._resolve(int(node_id)): proof_id for node_id, proof_id in proof_dict['node_refutations'].items()
        }

        prior_loops_cache = {int(k): v for k, v in proof_dict.get('loops_cache', {}).items()}

        return APRProof(
            id=id,
            kcfg=kcfg,
            terminal=terminal,
            init=init,
            target=target,
            bounded=bounded,
            bmc_depth=bmc_depth,
            logs=logs,
            circularity=circularity,
            admitted=admitted,
            proof_dir=proof_dir,
            subproof_ids=subproof_ids,
            node_refutations=node_refutations,
            prior_loops_cache=prior_loops_cache,
            _exec_time=exec_time,
        )

    def write_proof_data(self) -> None:
        if self.proof_dir is None or self.proof_subdir is None:
            _LOGGER.info(f'Skipped saving proof {self.id} since no save dir was specified.')
            return
        ensure_dir_path(self.proof_dir)
        ensure_dir_path(self.proof_subdir)
        proof_json = self.proof_subdir / 'proof.json'
        dct: dict[str, Any] = {}

        dct['id'] = self.id
        dct['subproof_ids'] = self.subproof_ids
        dct['admitted'] = self.admitted
        dct['execution_time'] = self._exec_time
        dct['type'] = 'APRProof'
        dct['init'] = self.kcfg._resolve(self.init)
        dct['target'] = self.kcfg._resolve(self.target)
        dct['terminal'] = sorted(node.id for node in self.kcfg.nodes if self.is_terminal(node.id))
        dct['node_refutations'] = {
            self.kcfg._resolve(node_id): proof.id for (node_id, proof) in self.node_refutations.items()
        }
        dct['circularity'] = self.circularity
        logs = {int(k): [l.to_dict() for l in ls] for k, ls in self.logs.items()}
        dct['logs'] = logs

        dct['bounded'] = sorted(self._bounded)
        if self.bmc_depth is not None:
            dct['bmc_depth'] = self.bmc_depth

        dct['loops_cache'] = self.prior_loops_cache

        proof_json.write_text(json.dumps(dct))
        _LOGGER.info(f'Wrote proof data for {self.id}: {proof_json}')
        self.kcfg.write_cfg_data()

    def refute_node(self, node: KCFG.Node) -> RefutationProof | None:
        _LOGGER.info(f'Attempting to refute node {node.id}')
        refutation = self.construct_node_refutation(node)
        if refutation is None:
            _LOGGER.error(f'Failed to refute node {node.id}')
            return None
        refutation.write_proof_data()

        self.node_refutations[node.id] = refutation

        self.write_proof_data()

        return refutation

    def unrefute_node(self, node: KCFG.Node) -> None:
        self.remove_subproof(self.get_refutation_id(node.id))
        del self.node_refutations[node.id]
        self.write_proof_data()
        _LOGGER.info(f'Disabled refutation of node {node.id}.')

    def construct_node_refutation(self, node: KCFG.Node) -> RefutationProof | None:  # TODO put into prover class
        if len(self.kcfg.successors(node.id)) > 0:
            _LOGGER.error(f'Cannot refute node {node.id} that already has successors')
            return None

        path = single(self.kcfg.paths_between(source_id=self.init, target_id=node.id))
        branches_on_path = list(filter(lambda x: type(x) is KCFG.Split or type(x) is KCFG.NDBranch, reversed(path)))
        if len(branches_on_path) == 0:
            _LOGGER.error(f'Cannot refute node {node.id} in linear KCFG')
            return None
        closest_branch = branches_on_path[0]
        if type(closest_branch) is KCFG.NDBranch:
            _LOGGER.error(f'Cannot refute node {node.id} following a non-deterministic branch: not yet implemented')
            return None

        assert type(closest_branch) is KCFG.Split
        refuted_branch_root = closest_branch.targets[0]
        csubst = closest_branch.splits[refuted_branch_root.id]
        if not (csubst.subst.is_identity):
            _LOGGER.error(
                f'Cannot refute node {node.id}: unexpected non-identity substitution {csubst.subst} in Split from {closest_branch.source.id}'
            )
            return None

        last_constraint = ml_pred_to_bool(csubst.constraint)
        relevant_vars = free_vars(last_constraint)
        pre_split_constraints = [
            ml_pred_to_bool(c)
            for c in remove_useless_constraints(closest_branch.source.cterm.constraints, relevant_vars)
        ]

        refutation_id = self.get_refutation_id(node.id)
        _LOGGER.info(f'Adding refutation proof {refutation_id} as subproof of {self.id}')
        refutation = RefutationProof(
            id=refutation_id,
            pre_constraints=pre_split_constraints,
            last_constraint=last_constraint,
            proof_dir=self.proof_dir,
        )

        self.add_subproof(refutation)
        return refutation


class APRProver(Prover[APRProof, APRProofStep, APRProofResult]):
    main_module_name: str
    execute_depth: int | None
    cut_point_rules: Iterable[str]
    terminal_rules: Iterable[str]
    counterexample_info: bool
    always_check_subsumption: bool
    fast_check_subsumption: bool
    kcfg_explore: KCFGExplore

    def __init__(
        self,
        kcfg_explore: KCFGExplore,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        counterexample_info: bool = False,
        always_check_subsumption: bool = True,
        fast_check_subsumption: bool = False,
    ) -> None:

        self.kcfg_explore = kcfg_explore
        self.main_module_name = self.kcfg_explore.cterm_symbolic._definition.main_module_name
        self.execute_depth = execute_depth
        self.cut_point_rules = cut_point_rules
        self.terminal_rules = terminal_rules
        self.counterexample_info = counterexample_info
        self.always_check_subsumption = always_check_subsumption
        self.fast_check_subsumption = fast_check_subsumption

    def close(self) -> None:
        self.kcfg_explore.cterm_symbolic._kore_client.close()

    def init_proof(self, proof: APRProof) -> None:
        def _inject_module(module_name: str, import_name: str, sentences: list[KRuleLike]) -> None:
            _module = KFlatModule(module_name, sentences, [KImport(import_name)])
            _kore_module = kflatmodule_to_kore(
                self.kcfg_explore.cterm_symbolic._definition, self.kcfg_explore.cterm_symbolic._kompiled_kore, _module
            )
            self.kcfg_explore.cterm_symbolic._kore_client.add_module(_kore_module, name_as_id=True)

        subproofs: list[Proof] = (
            [Proof.read_proof_data(proof.proof_dir, i) for i in proof.subproof_ids]
            if proof.proof_dir is not None
            else []
        )

        dependencies_as_rules: list[KRuleLike] = []
        for apr_subproof in [pf for pf in subproofs if isinstance(pf, APRProof)]:
            dependencies_as_rules.extend(apr_subproof.kcfg.to_rules(priority=20))
            if apr_subproof.admitted and len(apr_subproof.kcfg.predecessors(apr_subproof.target)) == 0:
                dependencies_as_rules.append(apr_subproof.as_rule(priority=20))
        circularity_rule = proof.as_rule(priority=20)

        _inject_module(proof.dependencies_module_name, self.main_module_name, dependencies_as_rules)
        _inject_module(proof.circularities_module_name, proof.dependencies_module_name, [circularity_rule])

        for node_id in [proof.init, proof.target]:
            if self.kcfg_explore.kcfg_semantics.is_terminal(proof.kcfg.node(node_id).cterm):
                proof.add_terminal(node_id)

    def _may_subsume(self, node: KCFG.Node, target_node: KCFG.Node) -> bool:
        node_k_cell = node.cterm.try_cell('K_CELL')
        target_k_cell = target_node.cterm.try_cell('K_CELL')
        if node_k_cell and target_k_cell and not target_k_cell.match(node_k_cell):
            return False
        return True

    def _check_subsume(self, node: KCFG.Node, target_node: KCFG.Node, proof_id: str) -> CSubst | None:
        target_cterm = target_node.cterm
        _LOGGER.debug(f'Checking subsumption into target state {proof_id}: {shorten_hashes((node.id, target_cterm))}')
        if self.fast_check_subsumption and not self._may_subsume(node, target_node):
            _LOGGER.info(f'Skipping full subsumption check because of fast may subsume check {proof_id}: {node.id}')
            return None
        _csubst = self.kcfg_explore.cterm_symbolic.implies(node.cterm, target_cterm)
        csubst = _csubst.csubst
        if csubst is not None:
            _LOGGER.info(f'Subsumed into target node {proof_id}: {shorten_hashes((node.id, target_node.id))}')
        return csubst

    def step_proof(self, step: APRProofStep) -> list[APRProofResult]:
        prior_loops: tuple[int, ...] = ()
        if step.bmc_depth is not None:
            for node in step.shortest_path_to_node:
                if self.kcfg_explore.kcfg_semantics.same_loop(node.cterm, step.node.cterm):
                    if node.id in step.prior_loops_cache:
                        prior_loops = step.prior_loops_cache[node.id] + (node.id,)
                        break

            _LOGGER.info(f'Prior loop heads for node {step.node.id}: {(step.node.id, prior_loops)}')
            if len(prior_loops) > step.bmc_depth:
                _LOGGER.warning(f'Bounded node {step.proof_id}: {step.node.id} at bmc depth {step.bmc_depth}')
                return [APRProofBoundedResult(node_id=step.node.id, prior_loops_cache_update=prior_loops)]

        # Terminal checks for current node and target node
        is_terminal = self.kcfg_explore.kcfg_semantics.is_terminal(step.node.cterm)
        target_is_terminal = self.kcfg_explore.kcfg_semantics.is_terminal(step.target.cterm)

        terminal_result: list[APRProofResult] = (
            [APRProofTerminalResult(node_id=step.node.id, prior_loops_cache_update=prior_loops)] if is_terminal else []
        )

        # Subsumption should be checked if and only if the target node
        # and the current node are either both terminal or both not terminal
        if is_terminal == target_is_terminal:
            csubst = self._check_subsume(step.node, step.target, proof_id=step.proof_id)
            if csubst is not None:
                # Information about the subsumed node being terminal must be returned
                # so that the set of terminal nodes is correctly updated
                return terminal_result + [
                    APRProofSubsumeResult(csubst=csubst, node_id=step.node.id, prior_loops_cache_update=prior_loops)
                ]

        if is_terminal:
            return terminal_result

        extend_result = self.kcfg_explore.extend_cterm(
            step.node.cterm,
            execute_depth=self.execute_depth,
            cut_point_rules=self.cut_point_rules,
            terminal_rules=self.terminal_rules,
            module_name=step.module_name,
            node_id=step.node.id,
        )
        return [
            APRProofExtendResult(
                node_id=step.node.id, extend_result=extend_result, prior_loops_cache_update=prior_loops
            )
        ]

    def failure_info(self, proof: APRProof) -> FailureInfo:
        return APRFailureInfo.from_proof(proof, self.kcfg_explore, counterexample_info=self.counterexample_info)


@dataclass(frozen=True)
class APRSummary(ProofSummary):
    id: str
    status: ProofStatus
    admitted: bool
    nodes: int
    pending: int
    failing: int
    vacuous: int
    stuck: int
    terminal: int
    refuted: int
    bmc_depth: int | None
    bounded: int
    subproofs: int
    formatted_exec_time: str

    @property
    def lines(self) -> list[str]:
        _lines = [
            f'APRProof: {self.id}',
            f'    status: {self.status}',
            f'    admitted: {self.admitted}',
            f'    nodes: {self.nodes}',
            f'    pending: {self.pending}',
            f'    failing: {self.failing}',
            f'    vacuous: {self.vacuous}',
            f'    stuck: {self.stuck}',
            f'    terminal: {self.terminal}',
            f'    refuted: {self.refuted}',
            f'    bounded: {self.bounded}',
            f'    execution time: {self.formatted_exec_time}',
        ]
        if self.bmc_depth is not None:
            _lines.append(f'    bmc depth: {self.bmc_depth}')
        _lines.append(f'Subproofs: {self.subproofs}')
        return _lines


@dataclass(frozen=True)
class APRFailureInfo(FailureInfo):
    pending_nodes: frozenset[int]
    failing_nodes: frozenset[int]
    path_conditions: FrozenDict[int, str]
    failure_reasons: FrozenDict[int, str]
    models: FrozenDict[int, frozenset[tuple[str, str]]]

    def __init__(
        self,
        failing_nodes: Iterable[int],
        pending_nodes: Iterable[int],
        path_conditions: Mapping[int, str],
        failure_reasons: Mapping[int, str],
        models: Mapping[int, Iterable[tuple[str, str]]],
    ):
        object.__setattr__(self, 'failing_nodes', frozenset(failing_nodes))
        object.__setattr__(self, 'pending_nodes', frozenset(pending_nodes))
        object.__setattr__(self, 'path_conditions', FrozenDict(path_conditions))
        object.__setattr__(self, 'failure_reasons', FrozenDict(failure_reasons))
        object.__setattr__(
            self, 'models', FrozenDict({node_id: frozenset(model) for (node_id, model) in models.items()})
        )

    @staticmethod
    def from_proof(proof: APRProof, kcfg_explore: KCFGExplore, counterexample_info: bool = False) -> APRFailureInfo:
        target = proof.kcfg.node(proof.target)
        pending_nodes = {node.id for node in proof.pending}
        failing_nodes = {node.id for node in proof.failing}
        path_conditions = {}
        failure_reasons = {}
        models = {}
        for node in proof.failing:
            node_cterm, _ = kcfg_explore.cterm_symbolic.simplify(node.cterm)
            target_cterm, _ = kcfg_explore.cterm_symbolic.simplify(target.cterm)
            _, reason = kcfg_explore.implication_failure_reason(node_cterm, target_cterm)
            path_condition = kcfg_explore.pretty_print(proof.path_constraints(node.id))
            failure_reasons[node.id] = reason
            path_conditions[node.id] = path_condition
            if counterexample_info:
                model_subst = kcfg_explore.cterm_symbolic.get_model(node.cterm)
                if type(model_subst) is Subst:
                    model: list[tuple[str, str]] = []
                    for var, term in model_subst.to_dict().items():
                        term_kast = KInner.from_dict(term)
                        term_pretty = kcfg_explore.pretty_print(term_kast)
                        model.append((var, term_pretty))
                    models[node.id] = model
        return APRFailureInfo(
            failing_nodes=failing_nodes,
            pending_nodes=pending_nodes,
            path_conditions=path_conditions,
            failure_reasons=failure_reasons,
            models=models,
        )

    def print(self) -> list[str]:
        res_lines: list[str] = []

        num_pending = len(self.pending_nodes)
        num_failing = len(self.failing_nodes)
        res_lines.append(
            f'{num_pending + num_failing} Failure nodes. ({num_pending} pending and {num_failing} failing)'
        )

        if num_pending > 0:
            res_lines.append('')
            res_lines.append(f'Pending nodes: {sorted(self.pending_nodes)}')

        if num_failing > 0:
            res_lines.append('')
            res_lines.append('Failing nodes:')
            for node_id in self.failing_nodes:
                reason = self.failure_reasons[node_id]
                path_condition = self.path_conditions[node_id]
                res_lines.append('')
                res_lines.append(f'  Node id: {str(node_id)}')

                res_lines.append('  Failure reason:')
                res_lines += [f'    {line}' for line in reason.split('\n')]

                res_lines.append('  Path condition:')
                res_lines += [f'    {path_condition}']

                if node_id in self.models:
                    res_lines.append('  Model:')
                    for var, term in self.models[node_id]:
                        res_lines.append(f'    {var} = {term}')
                else:
                    res_lines.append('  Failed to generate a model.')

            res_lines.append('')
            res_lines.append('Join the Runtime Verification Discord server for support: https://discord.gg/CurfmXNtbN')
        return res_lines
