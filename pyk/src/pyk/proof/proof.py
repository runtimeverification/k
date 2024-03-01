from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from itertools import chain
from typing import TYPE_CHECKING

from ..utils import ensure_dir_path, hash_file, hash_str

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final, TypeVar

    from pyk.kcfg.explore import KCFGExplore

    T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


class ProofStatus(Enum):
    PASSED = 'passed'
    FAILED = 'failed'
    PENDING = 'pending'


class Proof(ABC):
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
    def commit(self, result: StepResult) -> None:
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
    def status(self) -> ProofStatus:
        ...

    @property
    @abstractmethod
    def can_progress(self) -> bool:
        ...

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
    def from_dict(cls: type[Proof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> Proof:
        ...

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


class ProofSummary(ABC):
    id: str
    status: ProofStatus

    @property
    @abstractmethod
    def lines(self) -> list[str]:
        ...

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


class StepResult:
    ...


class FailureInfo:
    ...


class Prover:
    kcfg_explore: KCFGExplore
    proof: Proof

    def __init__(self, kcfg_explore: KCFGExplore):
        self.kcfg_explore = kcfg_explore

    @abstractmethod
    def failure_info(self) -> FailureInfo:
        ...

    @abstractmethod
    def step_proof(self) -> Iterable[StepResult]:
        ...

    def advance_proof(self, max_iterations: int | None = None, fail_fast: bool = False) -> None:
        iterations = 0
        while self.proof.can_progress:
            if fail_fast and self.proof.failed:
                _LOGGER.warning(f'Terminating proof early because fail_fast is set: {self.proof.id}')
                return
            if max_iterations is not None and max_iterations <= iterations:
                return
            iterations += 1
            results = self.step_proof()
            for result in results:
                self.proof.commit(result)
            if self.proof.failed:
                self.proof.failure_info = self.failure_info()
            self.proof.write_proof_data()
