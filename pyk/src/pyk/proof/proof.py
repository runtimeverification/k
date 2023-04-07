from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from enum import Enum
from typing import TYPE_CHECKING, Any, Dict, Final, Type, TypeVar

from ..utils import hash_str

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Optional

T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


class ProofStatus(Enum):
    PASSED = 'passed'
    FAILED = 'failed'
    PENDING = 'pending'


class Proof(ABC):
    id: str
    proof_dir: Optional[Path]

    def __init__(self, id: str, proof_dir: Optional[Path] = None) -> None:
        self.id = id
        self.proof_dir = proof_dir

    def write_proof(self) -> None:
        if not self.proof_dir:
            return
        proof_path = self.proof_dir / f'{hash_str(self.id)}.json'
        proof_path.write_text(json.dumps(self.dict))
        _LOGGER.info(f'Updated proof file {self.id}: {proof_path}')

    @property
    @abstractmethod
    def status(self) -> ProofStatus:
        ...

    @property
    @abstractmethod
    def dict(self) -> Dict[str, Any]:
        ...

    @classmethod
    @abstractmethod
    def from_dict(cls: Type[Proof], dct: Dict[str, Any]) -> Proof:
        ...
