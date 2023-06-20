from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from enum import Enum
from itertools import chain
from typing import TYPE_CHECKING

from ..utils import hash_file, hash_str

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final, TypeVar

    T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


class ProofStatus(Enum):
    PASSED = 'passed'
    FAILED = 'failed'
    PENDING = 'pending'


class Proof(ABC):
    _PROOF_TYPES: Final = {'APRProof', 'APRBMCProof', 'EqualityProof'}

    id: str
    proof_dir: Path | None
    _subproofs: dict[str, Proof]

    def __init__(self, id: str, proof_dir: Path | None = None, subproof_ids: Iterable[str] = ()) -> None:
        self.id = id
        self.proof_dir = proof_dir
        self._subproofs = {}
        if self.proof_dir is None and len(list(subproof_ids)) > 0:
            raise ValueError(f'Cannot read subproofs {subproof_ids} of proof {self.id} with no proof_dir')
        if len(list(subproof_ids)) > 0:
            for proof_id in subproof_ids:
                self.fetch_subproof(proof_id, force_reread=True)

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

    def add_subproof(self, proof_id: str) -> None:
        if self.proof_dir is None:
            raise ValueError(f'Cannot add subproof to the proof {self.id} with no proof_dir')
        assert self.proof_dir
        if not Proof.proof_exists(proof_id, self.proof_dir):
            raise ValueError(f"Cannot find subproof {proof_id} in parent proof's {self.id} proof_dir {self.proof_dir}")
        self._subproofs[proof_id] = self.fetch_subproof(proof_id, force_reread=True)

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

    @property
    def subproofs(self) -> Iterable[Proof]:
        """Return the subproofs, re-reading from disk the ones that changed"""
        return self._subproofs.values()

    @property
    def subproofs_status(self) -> ProofStatus:
        any_subproof_failed = any([p.status == ProofStatus.FAILED for p in self.subproofs])
        any_subproof_pending = any([p.status == ProofStatus.PENDING for p in self.subproofs])
        if any_subproof_failed:
            return ProofStatus.FAILED
        elif any_subproof_pending:
            return ProofStatus.PENDING
        else:
            return ProofStatus.PASSED

    @property
    @abstractmethod
    def status(self) -> ProofStatus:
        ...

    @property
    def dict(self) -> dict[str, Any]:
        return {
            'id': self.id,
            'subproof_ids': self.subproof_ids,
        }

    @classmethod
    @abstractmethod
    def from_dict(cls: type[Proof], dct: Mapping[str, Any]) -> Proof:
        ...

    @classmethod
    def read_proof(cls: type[Proof], id: str, proof_dir: Path) -> Proof:
        # these local imports allow us to call .to_dict() based on the proof type we read from JSON
        from .equality import EqualityProof  # noqa
        from .reachability import APRBMCProof, APRProof  # noqa

        proof_path = proof_dir / f'{hash_str(id)}.json'
        if Proof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            proof_type = proof_dict['type']
            _LOGGER.info(f'Reading {proof_type} from file {id}: {proof_path}')
            if proof_type in Proof._PROOF_TYPES:
                return locals()[proof_type].from_dict(proof_dict, proof_dir)

        raise ValueError(f'Could not load Proof from file {id}: {proof_path}')

    @property
    def json(self) -> str:
        return json.dumps(self.dict)

    @property
    def summary(self) -> Iterable[str]:
        subproofs_summaries = [subproof.summary for subproof in self.subproofs]
        return chain([f'Proof: {self.id}', f'    status: {self.status}'], *subproofs_summaries)
