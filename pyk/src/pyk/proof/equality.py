from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING

from ..kast.inner import KApply, KInner, KSort
from ..kast.manip import extract_lhs, extract_rhs, flatten_label
from ..prelude.kbool import BOOL, TRUE
from ..prelude.ml import is_top, mlAnd, mlEquals
from ..utils import hash_str
from .proof import Proof, ProofStatus

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final, TypeVar

    from ..kast.outer import KClaim, KDefinition
    from ..kcfg import KCFGExplore

    T = TypeVar('T', bound='Proof')

_LOGGER: Final = logging.getLogger(__name__)


class EqualityProof(Proof):
    lhs_body: KInner
    rhs_body: KInner
    sort: KSort
    lhs_constraints: tuple[KInner, ...]
    rhs_constraints: tuple[KInner, ...]
    simplified_equality: KInner | None

    def __init__(
        self,
        id: str,
        lhs_body: KInner,
        rhs_body: KInner,
        sort: KSort,
        lhs_constraints: Iterable[KInner] = (),
        rhs_constraints: Iterable[KInner] = (),
        simplified_equality: KInner | None = None,
        proof_dir: Path | None = None,
    ):
        super().__init__(id, proof_dir=proof_dir)
        self.lhs_body = lhs_body
        self.rhs_body = rhs_body
        self.sort = sort
        self.lhs_constraints = tuple(lhs_constraints)
        self.rhs_constraints = tuple(rhs_constraints)
        self.simplified_equality = simplified_equality

    @staticmethod
    def from_claim(claim: KClaim, defn: KDefinition) -> EqualityProof:
        lhs_body = extract_lhs(claim.body)
        rhs_body = extract_rhs(claim.body)
        assert type(lhs_body) is KApply
        sort = defn.return_sort(lhs_body.label)
        lhs_constraints = flatten_label('_andBool_', claim.requires)
        rhs_constraints = flatten_label('_andBool_', claim.ensures)
        return EqualityProof(
            claim.label, lhs_body, rhs_body, sort, lhs_constraints=lhs_constraints, rhs_constraints=rhs_constraints
        )

    @property
    def equality(self) -> KInner:
        lhs_ml_constraints: list[KInner] = [
            mlEquals(TRUE, c, arg_sort=BOOL, sort=self.sort) for c in self.lhs_constraints
        ]
        rhs_ml_constraints: list[KInner] = [
            mlEquals(TRUE, c, arg_sort=BOOL, sort=self.sort) for c in self.rhs_constraints
        ]
        lhs = mlAnd([self.lhs_body] + lhs_ml_constraints, sort=self.sort)
        rhs = mlAnd([self.rhs_body] + rhs_ml_constraints, sort=self.sort)
        return mlEquals(lhs, rhs, arg_sort=self.sort, sort=self.sort)

    def set_simplified(self, simplified: KInner) -> None:
        self.simplified_equality = simplified

    @staticmethod
    def read_proof(id: str, proof_dir: Path) -> EqualityProof:
        proof_path = proof_dir / f'{hash_str(id)}.json'
        if EqualityProof.proof_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            _LOGGER.info(f'Reading EqualityProof from file {id}: {proof_path}')
            return EqualityProof.from_dict(proof_dict, proof_dir=proof_dir)
        raise ValueError(f'Could not load EqualityProof from file {id}: {proof_path}')

    @property
    def status(self) -> ProofStatus:
        if self.simplified_equality is None:
            return ProofStatus.PENDING
        elif is_top(self.simplified_equality):
            return ProofStatus.PASSED
        else:
            return ProofStatus.FAILED

    @classmethod
    def from_dict(cls: type[EqualityProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> EqualityProof:
        id = dct['id']
        lhs_body = KInner.from_dict(dct['lhs_body'])
        rhs_body = KInner.from_dict(dct['rhs_body'])
        sort = KSort.from_dict(dct['sort'])
        lhs_constraints = [KInner.from_dict(c) for c in dct['lhs_constraints']]
        rhs_constraints = [KInner.from_dict(c) for c in dct['rhs_constraints']]
        simplified_equality = KInner.from_dict(dct['simplified_equality']) if 'simplified_equality' in dct else None
        return EqualityProof(
            id,
            lhs_body,
            rhs_body,
            sort,
            lhs_constraints=lhs_constraints,
            rhs_constraints=rhs_constraints,
            simplified_equality=simplified_equality,
            proof_dir=proof_dir,
        )

    @property
    def dict(self) -> dict[str, Any]:
        dct = {
            'type': 'EqualityProof',
            'id': self.id,
            'lhs_body': self.lhs_body.to_dict(),
            'rhs_body': self.rhs_body.to_dict(),
            'sort': self.sort.to_dict(),
            'lhs_constraints': [c.to_dict() for c in self.lhs_constraints],
            'rhs_constraints': [c.to_dict() for c in self.rhs_constraints],
        }
        if self.simplified_equality is not None:
            dct['simplified_equality'] = self.simplified_equality.to_dict()
        return dct

    @property
    def summary(self) -> Iterable[str]:
        return [
            f'EqualityProof: {self.id}',
            f'    status: {self.status}',
        ]


class EqualityProver:
    proof: EqualityProof

    def __init__(self, proof: EqualityProof) -> None:
        self.proof = proof

    def advance_proof(self, kcfg_explore: KCFGExplore) -> None:
        if not self.proof.status == ProofStatus.PENDING:
            return

        kore = kcfg_explore.kprint.kast_to_kore(self.proof.equality)
        _, kore_client = kcfg_explore._kore_rpc
        kore_simplified = kore_client.simplify(kore)
        kast_simplified = kcfg_explore.kprint.kore_to_kast(kore_simplified)
        self.proof.set_simplified(kast_simplified)

        self.proof.write_proof()
