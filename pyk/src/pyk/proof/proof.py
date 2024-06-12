from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from concurrent.futures import ThreadPoolExecutor, wait
from dataclasses import dataclass
from enum import Enum
from itertools import chain
from threading import current_thread
from typing import TYPE_CHECKING, ContextManager, Generic, TypeVar

from ..utils import ensure_dir_path, hash_file, hash_str

if TYPE_CHECKING:
    from collections.abc import Callable, Hashable, Iterable, Mapping
    from concurrent.futures import Executor, Future
    from pathlib import Path
    from typing import Any, Final

    T = TypeVar('T', bound='Proof')

P = TypeVar('P', bound='Proof')
PS = TypeVar('PS', bound='Hashable')
SR = TypeVar('SR')

_LOGGER: Final = logging.getLogger(__name__)


class ProofStatus(Enum):
    PASSED = 'passed'
    FAILED = 'failed'
    PENDING = 'pending'


class Proof(Generic[PS, SR]):
    """Abstract representation of a proof that can be executed in one or more discrete steps

    :param PS: Proof step: data required to perform a step of the proof.
    :param SR: Step result: data produced by executing a PS with `Prover.step_proof` used to update the `Proof`
    """

    _PROOF_TYPES: Final = {'APRProof', 'EqualityProof', 'RefutationProof'}

    id: str
    proof_dir: Path | None
    _subproofs: dict[str, Proof]
    admitted: bool
    failure_info: FailureInfo | None

    @property
    def proof_subdir(self) -> Path | None:
        if self.proof_dir is None:
            return None
        return self.proof_dir / self.id

    def __init__(
        self,
        id: str,
        proof_dir: Path | None = None,
        subproof_ids: Iterable[str] = (),
        admitted: bool = False,
    ) -> None:
        self.id = id
        self.admitted = admitted
        self.proof_dir = proof_dir
        self._subproofs = {}
        if self.proof_dir is None and len(list(subproof_ids)) > 0:
            raise ValueError(f'Cannot read subproofs {subproof_ids} of proof {self.id} with no proof_dir')
        if len(list(subproof_ids)) > 0:
            for proof_id in subproof_ids:
                self.fetch_subproof_data(proof_id, force_reread=True)
        if proof_dir is not None:
            ensure_dir_path(proof_dir)
        if self.proof_dir is not None:
            ensure_dir_path(self.proof_dir)

    @abstractmethod
    def commit(self, result: SR) -> None:
        """Apply the step result of type `SR` to `self`, modifying `self`."""
        ...

    def admit(self) -> None:
        self.admitted = True

    @property
    def subproof_ids(self) -> list[str]:
        return [sp.id for sp in self._subproofs.values()]

    def write_proof(self, subproofs: bool = False) -> None:
        if not self.proof_dir:
            return
        proof_path = self.proof_dir / f'{hash_str(self.id)}.json'
        if not self.up_to_date:
            proof_json = json.dumps(self.dict)
            proof_path.write_text(proof_json)
            _LOGGER.info(f'Updated proof file {self.id}: {proof_path}')
        if subproofs:
            for sp in self.subproofs:
                sp.write_proof(subproofs=subproofs)

    @staticmethod
    def proof_exists(id: str, proof_dir: Path) -> bool:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        return proof_path.exists() and proof_path.is_file()

    @staticmethod
    def proof_data_exists(id: str, proof_dir: Path) -> bool:
        proof_path = proof_dir / id / 'proof.json'
        return proof_path.exists() and proof_path.is_file()

    @property
    def digest(self) -> str:
        return hash_str(json.dumps(self.dict))

    @property
    def up_to_date(self) -> bool:
        """
        Check that the proof's representation on disk is up-to-date.
        """
        if self.proof_dir is None:
            raise ValueError(f'Cannot check if proof {self.id} with no proof_dir is up-to-date')
        proof_path = self.proof_dir / f'{hash_str(id)}.json'
        if proof_path.exists() and proof_path.is_file():
            return self.digest == hash_file(proof_path)
        else:
            return False

    def read_subproof(self, proof_id: str) -> None:
        if self.proof_dir is None:
            raise ValueError(f'Cannot add subproof to the proof {self.id} with no proof_dir')
        assert self.proof_dir
        if not Proof.proof_exists(proof_id, self.proof_dir):
            raise ValueError(f"Cannot find subproof {proof_id} in parent proof's {self.id} proof_dir {self.proof_dir}")
        self._subproofs[proof_id] = self.fetch_subproof(proof_id, force_reread=True)

    def read_subproof_data(self, proof_id: str) -> None:
        if self.proof_dir is None:
            raise ValueError(f'Cannot add subproof to the proof {self.id} with no proof_dir')
        assert self.proof_dir
        if not Proof.proof_data_exists(proof_id, self.proof_dir):
            raise ValueError(f"Cannot find subproof {proof_id} in parent proof's {self.id} proof_dir {self.proof_dir}")
        self._subproofs[proof_id] = self.fetch_subproof_data(proof_id, force_reread=True)

    def add_subproof(self, proof: Proof) -> None:
        self._subproofs[proof.id] = proof

    def remove_subproof(self, proof_id: str) -> None:
        del self._subproofs[proof_id]

    def fetch_subproof(
        self, proof_id: str, force_reread: bool = False, uptodate_check_method: str = 'timestamp'
    ) -> Proof:
        """Get a subproof, re-reading from disk if it's not up-to-date"""

        if self.proof_dir is not None and (force_reread or not self._subproofs[proof_id].up_to_date):
            updated_subproof = Proof.read_proof(proof_id, self.proof_dir)
            self._subproofs[proof_id] = updated_subproof
            return updated_subproof
        else:
            return self._subproofs[proof_id]

    def fetch_subproof_data(
        self, proof_id: str, force_reread: bool = False, uptodate_check_method: str = 'timestamp'
    ) -> Proof:
        """Get a subproof, re-reading from disk if it's not up-to-date"""

        if self.proof_dir is not None and (force_reread or not self._subproofs[proof_id].up_to_date):
            updated_subproof = Proof.read_proof_data(self.proof_dir, proof_id)
            self._subproofs[proof_id] = updated_subproof
            return updated_subproof
        else:
            return self._subproofs[proof_id]

    @property
    def subproofs(self) -> Iterable[Proof]:
        """Return the subproofs, re-reading from disk the ones that changed"""
        return self._subproofs.values()

    @property
    def subproofs_status(self) -> ProofStatus:
        if any(p.failed for p in self.subproofs):
            return ProofStatus.FAILED
        elif all(p.passed for p in self.subproofs):
            return ProofStatus.PASSED
        else:
            return ProofStatus.PENDING

    @property
    @abstractmethod
    def own_status(self) -> ProofStatus: ...

    @property
    def status(self) -> ProofStatus:
        if self.admitted:
            return ProofStatus.PASSED
        if self.own_status == ProofStatus.FAILED or self.subproofs_status == ProofStatus.FAILED:
            return ProofStatus.FAILED
        if self.own_status == ProofStatus.PENDING or self.subproofs_status == ProofStatus.PENDING:
            return ProofStatus.PENDING
        return ProofStatus.PASSED

    @property
    @abstractmethod
    def can_progress(self) -> bool: ...

    @property
    def failed(self) -> bool:
        return self.status == ProofStatus.FAILED

    @property
    def passed(self) -> bool:
        return self.status == ProofStatus.PASSED

    @property
    def dict(self) -> dict[str, Any]:
        return {
            'id': self.id,
            'subproof_ids': self.subproof_ids,
            'admitted': self.admitted,
        }

    @classmethod
    @abstractmethod
    def from_dict(cls: type[Proof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> Proof: ...

    @classmethod
    def read_proof(cls: type[Proof], id: str, proof_dir: Path) -> Proof:
        # these local imports allow us to call .to_dict() based on the proof type we read from JSON
        from .implies import EqualityProof, RefutationProof  # noqa
        from .reachability import APRProof  # noqa

        proof_path = proof_dir / f'{hash_str(id)}.json'
        if Proof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            proof_type = proof_dict['type']
            admitted = proof_dict.get('admitted', False)
            _LOGGER.info(f'Reading {proof_type} from file {id}: {proof_path}')
            if proof_type in Proof._PROOF_TYPES:
                return locals()[proof_type].from_dict(proof_dict, proof_dir)

        raise ValueError(f'Could not load Proof from file {id}: {proof_path}')

    @staticmethod
    def read_proof_data(proof_dir: Path, id: str) -> Proof:
        # these local imports allow us to call .to_dict() based on the proof type we read from JSON
        from .implies import EqualityProof, RefutationProof  # noqa
        from .reachability import APRProof  # noqa

        proof_path = proof_dir / id / 'proof.json'
        if Proof.proof_data_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            proof_type = proof_dict['type']
            admitted = proof_dict.get('admitted', False)
            _LOGGER.info(f'Reading {proof_type} from file {id}: {proof_path}')
            if proof_type in Proof._PROOF_TYPES:
                return locals()[proof_type].read_proof_data(proof_dir, id)

        raise ValueError(f'Could not load Proof from file {id}: {proof_path}')

    @abstractmethod
    def write_proof_data(self) -> None:
        for sp in self.subproofs:
            sp.write_proof_data()

    @property
    def json(self) -> str:
        return json.dumps(self.dict)

    @property
    def summary(self) -> ProofSummary:
        @dataclass
        class BaseSummary(ProofSummary):
            id: str
            status: ProofStatus

            @property
            def lines(self) -> list[str]:
                return [f'Proof: {self.id}', f'    status: {self.status}']

        subproofs_summaries = [subproof.summary for subproof in self.subproofs]
        return CompositeSummary([BaseSummary(self.id, self.status), *subproofs_summaries])

    @abstractmethod
    def get_steps(self) -> Iterable[PS]:
        """Return all currently available steps associated with this Proof. Should not modify `self`."""
        ...


class ProofSummary(ABC):
    id: str
    status: ProofStatus

    @property
    @abstractmethod
    def lines(self) -> list[str]: ...

    def __str__(self) -> str:
        return '\n'.join(self.lines)


@dataclass
class CompositeSummary(ProofSummary):
    summaries: tuple[ProofSummary, ...]

    def __init__(self, _summaries: Iterable[ProofSummary]):
        self.summaries = tuple(chain(_summaries))

    def __str__(self) -> str:
        return '\n'.join(str(summary) for summary in self.summaries)

    @property
    def lines(self) -> list[str]:
        return [line for lines in (summary.lines for summary in self.summaries) for line in lines]


class FailureInfo: ...


def parallel_advance_proof(
    proof: P,
    create_prover: Callable[[], Prover[P, PS, SR]],
    max_iterations: int | None = None,
    fail_fast: bool = False,
    max_workers: int = 1,
) -> None:
    """Advance proof with multithreaded strategy: `Prover.step_proof()` to a worker thread pool for each step
    as available, and `Proof.commit()` results as they become available, and get new steps with
    `Proof.get_steps()` and submit to thread pool.

    :param P: Type of proof to be advanced in parallel
    :param PS: Proof step: data required to perform a step of the proof.
    :param SR: Step result: data produced by executing a PS with `Prover.step_proof` used to update the `Proof`

    :param create_prover: Function which creates a new `Prover`. These provers must not reference any shared
        data to be written during `parallel_advance_proof`, to avoid race conditions.
    :param max_iterations: Maximum number of steps to take
    :param fail_fast: If the proof is failing after finishing a step, halt execution even if there are
        still available steps
    :param max_workers: Maximum number of worker threads the pool can spawn
    """

    pending: set[Future[Any]] = set()
    explored: set[PS] = set()
    iterations = 0

    with create_prover() as main_prover:
        main_prover.init_proof(proof)

        with _ProverPool[P, PS, SR](create_prover=create_prover, max_workers=max_workers) as pool:

            def submit_steps(_steps: Iterable[PS]) -> None:
                for step in _steps:
                    if step in explored:
                        continue
                    explored.add(step)
                    future: Future[Any] = pool.submit(step)  # <-- schedule steps for execution
                    pending.add(future)

            submit_steps(proof.get_steps())

            while True:
                if not pending:
                    break
                done, _ = wait(pending, return_when='FIRST_COMPLETED')
                future = done.pop()
                proof_results = future.result()
                for result in proof_results:
                    proof.commit(result)
                proof.write_proof_data()
                iterations += 1
                if max_iterations is not None and max_iterations <= iterations:
                    break
                if fail_fast and proof.failed:
                    _LOGGER.warning(f'Terminating proof early because fail_fast is set: {proof.id}')
                    break
                submit_steps(proof.get_steps())
                pending.remove(future)

            if proof.failed:
                proof.failure_info = main_prover.failure_info(proof)
            proof.write_proof_data()


class _ProverPool(ContextManager['_ProverPool'], Generic[P, PS, SR]):
    """Wrapper for `ThreadPoolExecutor` which spawns one `Prover` for each worker thread.

    :param P: Type of proof to be advanced in parallel
    :param PS: Proof step: data required to perform a step of the proof.
    :param SR: Step result: data produced by executing a PS with `Prover.step_proof` used to update the `Proof`

    :param create_prover: Function which creates a new `Prover`. These provers must not reference any shared
        data to be written during `parallel_advance_proof`, to avoid race conditions.
    :param max_workers: Maximum number of worker threads the pool can spawn

    """

    _create_prover: Callable[[], Prover[P, PS, SR]]
    _provers: dict[str, Prover[P, PS, SR]]
    _executor: Executor
    _closed: bool

    def __init__(
        self,
        create_prover: Callable[[], Prover[P, PS, SR]],
        *,
        max_workers: int | None = None,
    ) -> None:
        self._create_prover = create_prover
        self._provers = {}
        self._executor = ThreadPoolExecutor(max_workers)
        self._closed = False

    def __enter__(self) -> _ProverPool[P, PS, SR]:
        self._executor.__enter__()
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        self._executor.__exit__(exc_type, exc_val, exc_tb)
        self.close()

    def close(self) -> None:
        self._closed = True
        for prover in self._provers.values():
            prover.close()

    def submit(self, proof_step: PS) -> Future[Iterable[SR]]:
        if self._closed:
            raise ValueError('ProverPool has been closed')
        return self._executor.submit(self._with_prover(proof_step))

    def _with_prover(self, proof_step: PS) -> Callable[[], Iterable[SR]]:

        def step() -> Iterable[SR]:
            thread_name = current_thread().name
            prover: Prover[P, PS, SR] | None = self._provers.get(thread_name)
            if prover is None:
                prover = self._create_prover()
                self._provers[thread_name] = prover
            return prover.step_proof(proof_step)

        return step


class Prover(ContextManager['Prover'], Generic[P, PS, SR]):
    """Abstract class which advances `Proof`s with `init_proof()` and `step_proof()`
    :param P: Type of proof this `Prover` operates on
    :param PS: Proof step: data required to perform a step of the proof.
    :param SR: Step result: data produced by executing a PS with `Prover.step_proof` used to update the `Proof`
    """

    def __enter__(self) -> Prover[P, PS, SR]:
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        self.close()

    @abstractmethod
    def close(self) -> None: ...

    @abstractmethod
    def failure_info(self, proof: P) -> FailureInfo: ...

    @abstractmethod
    def step_proof(self, step: PS) -> Iterable[SR]:
        """Do the work associated with a `PS`, a proof step. Should not modify a `Proof` or `self`, but may read
        from `self` as long as those fields are not being modified during `step_proof()`, `get_steps()`, and
        `commit()`.
        """
        ...

    @abstractmethod
    def init_proof(self, proof: P) -> None:
        """Perform any initialization steps needed at the beginning of proof execution. For example,  for
        `APRProver`, upload circularity and depends module of the proof to the KoreServer via `add_module`.
        """
        ...

    def advance_proof(self, proof: P, max_iterations: int | None = None, fail_fast: bool = False) -> None:
        """Advance proof by a simple loop of `Proof.get_steps()` -> `Prover.step_proof()` -> `Proof.commit()`

        :param max_iterations: Maximum number of steps to take
        :param fail_fast: If the proof is failing after finishing a step, halt execution even if there are
            still available steps
        """
        iterations = 0
        _LOGGER.info(f'Initializing proof: {proof.id}')
        self.init_proof(proof)
        while True:
            steps = list(proof.get_steps())
            _LOGGER.info(f'Found {len(steps)} next steps for proof: {proof.id}')
            if len(steps) == 0:
                break
            for step in steps:
                if fail_fast and proof.failed:
                    _LOGGER.warning(f'Terminating proof early because fail_fast is set: {proof.id}')
                    proof.failure_info = self.failure_info(proof)
                    return
                if max_iterations is not None and max_iterations <= iterations:
                    return
                iterations += 1
                results = self.step_proof(step)
                for result in results:
                    proof.commit(result)
                proof.write_proof_data()
        if proof.failed:
            proof.failure_info = self.failure_info(proof)
