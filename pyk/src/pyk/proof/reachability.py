from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING

from ..kcfg import KCFG
from ..utils import hash_str, shorten_hashes
from .proof import Proof, ProofStatus

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final, TypeVar

    from ..cterm import CTerm
    from ..kast.inner import KInner
    from ..kcfg import KCFGExplore

    T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


class AGProof(Proof):
    kcfg: KCFG

    def __init__(self, id: str, kcfg: KCFG, proof_dir: Path | None = None):
        super().__init__(id, proof_dir=proof_dir)
        self.kcfg = kcfg

    @staticmethod
    def read_proof(id: str, proof_dir: Path) -> AGProof:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        if AGProof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            _LOGGER.info(f'Reading AGProof from file {id}: {proof_path}')
            return AGProof.from_dict(proof_dict, proof_dir=proof_dir)
        raise ValueError(f'Could not load AGProof from file {id}: {proof_path}')

    @property
    def status(self) -> ProofStatus:
        if len(self.kcfg.stuck) > 0:
            return ProofStatus.FAILED
        elif len(self.kcfg.frontier) > 0:
            return ProofStatus.PENDING
        else:
            return ProofStatus.PASSED

    @classmethod
    def from_dict(cls: type[AGProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> AGProof:
        cfg = KCFG.from_dict(dct['cfg'])
        id = dct['id']
        return AGProof(id, cfg, proof_dir=proof_dir)

    @property
    def dict(self) -> dict[str, Any]:
        return {'type': 'AGProof', 'id': self.id, 'cfg': self.kcfg.to_dict()}

    @property
    def summary(self) -> Iterable[str]:
        return [
            f'AGProof: {self.id}',
            f'    status: {self.status}',
            f'    nodes: {len(self.kcfg.nodes)}',
            f'    frontier: {len(self.kcfg.frontier)}',
            f'    stuck: {len(self.kcfg.stuck)}',
        ]


class AGBMCProof(AGProof):
    bmc_depth: int
    _bounded_states: list[str]

    def __init__(
        self,
        id: str,
        kcfg: KCFG,
        bmc_depth: int,
        bounded_states: Iterable[str] | None = None,
        proof_dir: Path | None = None,
    ):
        super().__init__(id, kcfg, proof_dir=proof_dir)
        self.bmc_depth = bmc_depth
        self._bounded_states = list(bounded_states) if bounded_states is not None else []

    @staticmethod
    def read_proof(id: str, proof_dir: Path) -> AGBMCProof:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        if AGBMCProof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            _LOGGER.info(f'Reading AGBMCProof from file {id}: {proof_path}')
            return AGBMCProof.from_dict(proof_dict, proof_dir=proof_dir)
        raise ValueError(f'Could not load AGBMCProof from file {id}: {proof_path}')

    @property
    def status(self) -> ProofStatus:
        if any(nd.id not in self._bounded_states for nd in self.kcfg.stuck):
            return ProofStatus.FAILED
        elif len(self.kcfg.frontier) > 0:
            return ProofStatus.PENDING
        else:
            return ProofStatus.PASSED

    @classmethod
    def from_dict(cls: type[AGBMCProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> AGBMCProof:
        cfg = KCFG.from_dict(dct['cfg'])
        id = dct['id']
        bounded_states = dct['bounded_states']
        bmc_depth = dct['bmc_depth']
        return AGBMCProof(id, cfg, bmc_depth, bounded_states=bounded_states, proof_dir=proof_dir)

    @property
    def dict(self) -> dict[str, Any]:
        return {
            'type': 'AGBMCProof',
            'id': self.id,
            'cfg': self.kcfg.to_dict(),
            'bmc_depth': self.bmc_depth,
            'bounded_states': self._bounded_states,
        }

    def bound_state(self, nid: str) -> None:
        self._bounded_states.append(nid)

    @property
    def summary(self) -> Iterable[str]:
        return [
            f'AGBMCProof(depth={self.bmc_depth}): {self.id}',
            f'    status: {self.status}',
            f'    nodes: {len(self.kcfg.nodes)}',
            f'    frontier: {len(self.kcfg.frontier)}',
            f'    stuck: {len([nd for nd in self.kcfg.stuck if nd.id not in self._bounded_states])}',
            f'    bmc-depth-bounded: {len(self._bounded_states)}',
        ]


class AGProver:
    proof: AGProof
    _is_terminal: Callable[[CTerm], bool] | None
    _extract_branches: Callable[[CTerm], Iterable[KInner]] | None

    def __init__(
        self,
        proof: AGProof,
        is_terminal: Callable[[CTerm], bool] | None = None,
        extract_branches: Callable[[CTerm], Iterable[KInner]] | None = None,
    ) -> None:
        self.proof = proof
        self._is_terminal = is_terminal
        self._extract_branches = extract_branches

    def _check_terminal(self, curr_node: KCFG.Node) -> bool:
        if self._is_terminal is not None:
            _LOGGER.info(f'Checking terminal {self.proof.id}: {shorten_hashes(curr_node.id)}')
            if self._is_terminal(curr_node.cterm):
                _LOGGER.info(f'Terminal node {self.proof.id}: {shorten_hashes(curr_node.id)}.')
                self.proof.kcfg.add_expanded(curr_node.id)
                return True
        return False

    def advance_proof(
        self,
        kcfg_explore: KCFGExplore,
        max_iterations: int | None = None,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        implication_every_block: bool = True,
    ) -> KCFG:
        iterations = 0

        while self.proof.kcfg.frontier:
            self.proof.write_proof()

            if max_iterations is not None and max_iterations <= iterations:
                _LOGGER.warning(f'Reached iteration bound {self.proof.id}: {max_iterations}')
                break
            iterations += 1
            curr_node = self.proof.kcfg.frontier[0]

            if kcfg_explore.target_subsume(self.proof.kcfg, curr_node):
                continue

            if self._check_terminal(curr_node):
                continue

            if self._extract_branches is not None:
                branches = list(self._extract_branches(curr_node.cterm))
                if len(branches) > 0:
                    self.proof.kcfg.split_on_constraints(curr_node.id, branches)
                    _LOGGER.info(
                        f'Found {len(branches)} branches using heuristic for node {self.proof.id}: {shorten_hashes(curr_node.id)}: {[kcfg_explore.kprint.pretty_print(bc) for bc in branches]}'
                    )
                    continue

            kcfg_explore.extend(
                self.proof.kcfg,
                curr_node,
                execute_depth=execute_depth,
                cut_point_rules=cut_point_rules,
                terminal_rules=terminal_rules,
            )

        self.proof.write_proof()
        return self.proof.kcfg


class AGBMCProver(AGProver):
    proof: AGBMCProof
    _same_loop: Callable[[CTerm, CTerm], bool]
    _checked_nodes: list[str]

    def __init__(
        self,
        proof: AGBMCProof,
        same_loop: Callable[[CTerm, CTerm], bool],
        is_terminal: Callable[[CTerm], bool] | None = None,
        extract_branches: Callable[[CTerm], Iterable[KInner]] | None = None,
    ) -> None:
        super().__init__(proof, is_terminal=is_terminal, extract_branches=extract_branches)
        self._same_loop = same_loop
        self._checked_nodes = []

    def advance_proof(
        self,
        kcfg_explore: KCFGExplore,
        max_iterations: int | None = None,
        execute_depth: int | None = None,
        cut_point_rules: Iterable[str] = (),
        terminal_rules: Iterable[str] = (),
        implication_every_block: bool = True,
    ) -> KCFG:
        iterations = 0

        while self.proof.kcfg.frontier:
            self.proof.write_proof()

            if max_iterations is not None and max_iterations <= iterations:
                _LOGGER.warning(f'Reached iteration bound {self.proof.id}: {max_iterations}')
                break
            iterations += 1

            for f in self.proof.kcfg.frontier:
                if f.id not in self._checked_nodes:
                    self._checked_nodes.append(f.id)
                    prior_loops = [
                        nd.id
                        for nd in self.proof.kcfg.reachable_nodes(f.id, reverse=True, traverse_covers=True)
                        if nd.id != f.id and self._same_loop(nd.cterm, f.cterm)
                    ]
                    if len(prior_loops) >= self.proof.bmc_depth:
                        self.proof.kcfg.add_expanded(f.id)
                        self.proof.bound_state(f.id)

            super().advance_proof(
                kcfg_explore,
                max_iterations=1,
                execute_depth=execute_depth,
                cut_point_rules=cut_point_rules,
                terminal_rules=terminal_rules,
                implication_every_block=implication_every_block,
            )

        self.proof.write_proof()
        return self.proof.kcfg
