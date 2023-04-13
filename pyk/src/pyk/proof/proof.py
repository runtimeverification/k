from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from enum import Enum
from typing import TYPE_CHECKING

from ..utils import hash_str

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
    id: str
    proof_dir: Path | None

    def __init__(self, id: str, proof_dir: Path | None = None) -> None:
        self.id = id
        self.proof_dir = proof_dir

    def write_proof(self) -> None:
        if not self.proof_dir:
            return
        proof_path = self.proof_dir / f'{hash_str(self.id)}.json'
        proof_path.write_text(json.dumps(self.dict))
        _LOGGER.info(f'Updated proof file {self.id}: {proof_path}')

    @staticmethod
    def proof_exists(id: str, proof_dir: Path) -> bool:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        return proof_path.exists() and proof_path.is_file()

    @property
    @abstractmethod
    def status(self) -> ProofStatus:
        ...

    @property
    @abstractmethod
    def dict(self) -> dict[str, Any]:
        ...

    @classmethod
    @abstractmethod
    def from_dict(cls: type[Proof], dct: Mapping[str, Any]) -> Proof:
        ...

    @property
    def summary(self) -> Iterable[str]:
        return [self.id]
