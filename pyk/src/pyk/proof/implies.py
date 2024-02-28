from __future__ import annotations

import json
import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Final

from ..cterm import CSubst, CTerm
from ..kast.inner import KApply, KInner, Subst
from ..kast.manip import extract_lhs, extract_rhs, flatten_label
from ..prelude.k import GENERATED_TOP_CELL
from ..prelude.kbool import BOOL, TRUE
from ..prelude.ml import is_bottom, is_top, mlAnd, mlEquals, mlEqualsFalse, mlEqualsTrue
from ..utils import ensure_dir_path
from .proof import Proof, ProofStatus, ProofSummary, Prover

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path

    from ..kast.inner import KSort
    from ..kast.outer import KClaim, KDefinition
    from ..kcfg import KCFGExplore
    from ..ktool.kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


class ImpliesProof(Proof):
    antecedent: KInner
    consequent: KInner
    bind_universally: bool
    simplified_antecedent: KInner | None
    simplified_consequent: KInner | None
    csubst: CSubst | None

    def __init__(
        self,
        id: str,
        antecedent: KInner,
        consequent: KInner,
        bind_universally: bool = False,
        simplified_antecedent: KInner | None = None,
        simplified_consequent: KInner | None = None,
        csubst: CSubst | None = None,
        proof_dir: Path | None = None,
        subproof_ids: Iterable[str] = (),
        admitted: bool = False,
    ):
        super().__init__(id=id, proof_dir=proof_dir, subproof_ids=subproof_ids, admitted=admitted)
        self.antecedent = antecedent
        self.consequent = consequent
        self.bind_universally = bind_universally
        self.simplified_antecedent = simplified_antecedent
        self.simplified_consequent = simplified_consequent
        self.csubst = csubst

    @property
    def status(self) -> ProofStatus:
        if self.admitted:
            return ProofStatus.PASSED
        if self.simplified_antecedent is None or self.simplified_consequent is None:
            return ProofStatus.PENDING
        elif self.csubst is None:
            return ProofStatus.FAILED
        else:
            return ProofStatus.PASSED

    @property
    def can_progress(self) -> bool:
        return self.simplified_antecedent is None or self.simplified_consequent is None

    def write_proof_data(self, subproofs: bool = False) -> None:
        super().write_proof_data()
        if not self.proof_dir:
            return
        ensure_dir_path(self.proof_dir)
        ensure_dir_path(self.proof_dir / self.id)
        proof_path = self.proof_dir / self.id / 'proof.json'
        if not self.up_to_date:
            proof_json = json.dumps(self.dict)
            proof_path.write_text(proof_json)
            _LOGGER.info(f'Updated proof file {self.id}: {proof_path}')

    @classmethod
    def from_dict(cls: type[ImpliesProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> ImpliesProof:
        id = dct['id']
        antecedent = KInner.from_dict(dct['antecedent'])
        consequent = KInner.from_dict(dct['consequent'])
        simplified_antecedent = (
            KInner.from_dict(dct['simplified_antecedent']) if 'simplified_antecedent' in dct else None
        )
        simplified_consequent = (
            KInner.from_dict(dct['simplified_consequent']) if 'simplified_consequent' in dct else None
        )
        csubst = CSubst.from_dict(dct['csubst']) if 'csubst' in dct else None
        subproof_ids = dct['subproof_ids']
        admitted = dct.get('admitted', False)
        return ImpliesProof(
            id,
            antecedent,
            consequent,
            simplified_antecedent=simplified_antecedent,
            simplified_consequent=simplified_consequent,
            csubst=csubst,
            admitted=admitted,
            subproof_ids=subproof_ids,
            proof_dir=proof_dir,
        )

    @property
    def dict(self) -> dict[str, Any]:
        dct = super().dict
        dct['type'] = 'ImpliesProof'
        dct['antecedent'] = self.antecedent.to_dict()
        dct['consequent'] = self.consequent.to_dict()
        if self.simplified_antecedent is not None:
            dct['simplified_antecedent'] = self.simplified_antecedent.to_dict()
        if self.simplified_consequent is not None:
            dct['simplified_consequent'] = self.simplified_consequent.to_dict()
        if self.csubst is not None:
            dct['csubst'] = self.csubst.to_dict()
        return dct


class EqualityProof(ImpliesProof):
    def __init__(
        self,
        id: str,
        lhs_body: KInner,
        rhs_body: KInner,
        sort: KSort,
        constraints: Iterable[KInner] = (),
        simplified_constraints: KInner | None = None,
        simplified_equality: KInner | None = None,
        csubst: CSubst | None = None,
        proof_dir: Path | None = None,
        subproof_ids: Iterable[str] = (),
        admitted: bool = False,
    ):
        antecedent = mlAnd(constraints)
        consequent = mlEquals(lhs_body, rhs_body, arg_sort=sort, sort=GENERATED_TOP_CELL)
        super().__init__(
            id,
            antecedent,
            consequent,
            bind_universally=True,
            simplified_antecedent=simplified_constraints,
            simplified_consequent=simplified_equality,
            csubst=csubst,
            proof_dir=proof_dir,
            subproof_ids=subproof_ids,
            admitted=admitted,
        )
        _LOGGER.warning(
            'Building an EqualityProof that has known soundness issues: See https://github.com/runtimeverification/haskell-backend/issues/3605.'
        )

    @staticmethod
    def read_proof_data(proof_dir: Path, id: str) -> EqualityProof:
        proof_path = proof_dir / id / 'proof.json'
        if Proof.proof_data_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            return EqualityProof.from_dict(proof_dict, proof_dir)

        raise ValueError(f'Could not load Proof from file {id}: {proof_path}')

    @staticmethod
    def from_claim(claim: KClaim, defn: KDefinition, proof_dir: Path | None = None) -> EqualityProof:
        claim_body = defn.add_sort_params(claim.body)
        sort = defn.sort_strict(claim_body)
        lhs_body = extract_lhs(claim_body)
        rhs_body = extract_rhs(claim_body)
        if not (claim.ensures is None or claim.ensures == TRUE):
            raise ValueError(f'Cannot convert claim to EqualityProof due to non-trival ensures clause {claim.ensures}')
        constraints = [mlEquals(TRUE, c, arg_sort=BOOL) for c in flatten_label('_andBool_', claim.requires)]
        return EqualityProof(claim.label, lhs_body, rhs_body, sort, constraints=constraints, proof_dir=proof_dir)

    @property
    def equality(self) -> KApply:
        assert type(self.consequent) is KApply
        return self.consequent

    @property
    def lhs_body(self) -> KInner:
        return self.equality.args[0]

    @property
    def rhs_body(self) -> KInner:
        return self.equality.args[1]

    @property
    def sort(self) -> KSort:
        return self.equality.label.params[0]

    @property
    def constraint(self) -> KInner:
        return self.antecedent

    @property
    def constraints(self) -> list[KInner]:
        return flatten_label('#And', self.constraint)

    @property
    def simplified_constraints(self) -> KInner | None:
        return self.simplified_antecedent

    @property
    def simplified_equality(self) -> KInner | None:
        return self.simplified_consequent

    @classmethod
    def from_dict(cls: type[EqualityProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> EqualityProof:
        implies_proof = ImpliesProof.from_dict(dct, proof_dir=proof_dir)
        assert type(implies_proof.consequent) is KApply
        return EqualityProof(
            id=implies_proof.id,
            lhs_body=implies_proof.consequent.args[0],
            rhs_body=implies_proof.consequent.args[1],
            sort=implies_proof.consequent.label.params[0],
            constraints=flatten_label('#And', implies_proof.antecedent),
            simplified_constraints=implies_proof.simplified_antecedent,
            simplified_equality=implies_proof.simplified_consequent,
            csubst=implies_proof.csubst,
            proof_dir=implies_proof.proof_dir,
            subproof_ids=implies_proof.subproof_ids,
            admitted=implies_proof.admitted,
        )

    @property
    def dict(self) -> dict[str, Any]:
        dct = super().dict
        dct['type'] = 'EqualityProof'
        return dct

    def pretty(self, kprint: KPrint) -> Iterable[str]:
        lines = [
            f'LHS: {kprint.pretty_print(self.lhs_body)}',
            f'RHS: {kprint.pretty_print(self.rhs_body)}',
            f'Constraints: {kprint.pretty_print(mlAnd(self.constraints))}',
            f'Equality: {kprint.pretty_print(self.equality)}',
        ]
        if self.simplified_constraints:
            lines.append(f'Simplified constraints: {kprint.pretty_print(self.simplified_constraints)}')
        if self.simplified_equality:
            lines.append(f'Simplified equality: {kprint.pretty_print(self.simplified_equality)}')
        if self.csubst is not None:
            lines.append(f'Implication csubst: {self.csubst}')
        lines.append(f'Status: {self.status}')
        return lines

    @property
    def summary(self) -> EqualitySummary:
        return EqualitySummary(self.id, self.status, self.admitted)


@dataclass(frozen=True)
class EqualitySummary(ProofSummary):
    id: str
    status: ProofStatus
    admitted: bool

    @property
    def lines(self) -> list[str]:
        return [
            f'EqualityProof: {self.id}',
            f'    status: {self.status}',
            f'    admitted: {self.admitted}',
        ]


class RefutationProof(ImpliesProof):
    def __init__(
        self,
        id: str,
        pre_constraints: Iterable[KInner],
        last_constraint: KInner,
        simplified_antecedent: KInner | None = None,
        simplified_consequent: KInner | None = None,
        csubst: CSubst | None = None,
        proof_dir: Path | None = None,
        subproof_ids: Iterable[str] = (),
        admitted: bool = False,
    ):
        antecedent = mlAnd(mlEqualsTrue(c) for c in pre_constraints)
        consequent = mlEqualsFalse(last_constraint)
        super().__init__(
            id,
            antecedent,
            consequent,
            bind_universally=True,
            simplified_antecedent=simplified_antecedent,
            simplified_consequent=simplified_consequent,
            csubst=csubst,
            subproof_ids=subproof_ids,
            proof_dir=proof_dir,
            admitted=admitted,
        )
        _LOGGER.warning(
            'Building a RefutationProof that has known soundness issues: See https://github.com/runtimeverification/haskell-backend/issues/3605.'
        )

    @staticmethod
    def read_proof_data(proof_dir: Path, id: str) -> RefutationProof:
        proof_path = proof_dir / id / 'proof.json'
        if Proof.proof_data_exists(id, proof_dir):
            proof_dict = json.loads(proof_path.read_text())
            return RefutationProof.from_dict(proof_dict, proof_dir)

        raise ValueError(f'Could not load Proof from file {id}: {proof_path}')

    @property
    def pre_constraints(self) -> list[KInner]:
        return flatten_label('#And', self.antecedent)

    @property
    def last_constraint(self) -> KInner:
        assert type(self.consequent) is KApply
        return self.consequent.args[1]

    @property
    def simplified_constraints(self) -> KInner | None:
        return self.simplified_antecedent

    @classmethod
    def from_dict(cls: type[RefutationProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> RefutationProof:
        implies_proof = ImpliesProof.from_dict(dct, proof_dir=proof_dir)
        assert type(implies_proof.consequent) is KApply
        return RefutationProof(
            id=implies_proof.id,
            pre_constraints=flatten_label('#And', implies_proof.antecedent),
            last_constraint=implies_proof.consequent.args[1],
            simplified_antecedent=implies_proof.simplified_antecedent,
            simplified_consequent=implies_proof.simplified_consequent,
            csubst=implies_proof.csubst,
            proof_dir=implies_proof.proof_dir,
            subproof_ids=implies_proof.subproof_ids,
            admitted=implies_proof.admitted,
        )

    @property
    def dict(self) -> dict[str, Any]:
        dct = super().dict
        dct['type'] = 'RefutationProof'
        return dct

    @property
    def summary(self) -> RefutationSummary:
        return RefutationSummary(self.id, self.status)

    def pretty(self, kprint: KPrint) -> Iterable[str]:
        lines = [
            f'Constraints: {kprint.pretty_print(mlAnd(self.pre_constraints))}',
            f'Last constraint: {kprint.pretty_print(self.last_constraint)}',
        ]
        if self.csubst is not None:
            lines.append(f'Implication csubst: {self.csubst}')
        lines.append(f'Status: {self.status}')
        return lines


@dataclass(frozen=True)
class RefutationSummary(ProofSummary):
    id: str
    status: ProofStatus

    @property
    def lines(self) -> list[str]:
        return [
            f'RefutationProof: {self.id}',
            f'    status: {self.status}',
        ]


class ImpliesProver(Prover):
    proof: ImpliesProof

    def __init__(self, proof: ImpliesProof, kcfg_explore: KCFGExplore):
        super().__init__(kcfg_explore)
        self.proof = proof

    def step_proof(self) -> None:
        proof_type = type(self.proof).__name__
        _LOGGER.info(f'Attempting {proof_type} {self.proof.id}')

        if self.proof.status is not ProofStatus.PENDING:
            _LOGGER.info(f'{proof_type} finished {self.proof.id}: {self.proof.status}')
            return

        # to prove the equality, we check the implication of the form `constraints #Implies LHS #Equals RHS`, i.e.
        # "LHS equals RHS under these constraints"
        antecedent_simplified_kast, _ = self.kcfg_explore.cterm_symbolic.kast_simplify(self.proof.antecedent)
        consequent_simplified_kast, _ = self.kcfg_explore.cterm_symbolic.kast_simplify(self.proof.consequent)
        self.proof.simplified_antecedent = antecedent_simplified_kast
        self.proof.simplified_consequent = consequent_simplified_kast
        _LOGGER.info(f'Simplified antecedent: {self.kcfg_explore.pretty_print(antecedent_simplified_kast)}')
        _LOGGER.info(f'Simplified consequent: {self.kcfg_explore.pretty_print(consequent_simplified_kast)}')

        if is_bottom(antecedent_simplified_kast):
            _LOGGER.warning(f'Antecedent of implication (proof constraints) simplifies to #Bottom {self.proof.id}')
            self.proof.csubst = CSubst(Subst({}), ())

        elif is_top(consequent_simplified_kast):
            _LOGGER.warning(f'Consequent of implication (proof equality) simplifies to #Top {self.proof.id}')
            self.proof.csubst = CSubst(Subst({}), ())

        else:
            # TODO: we should not be forced to include the dummy configuration in the antecedent and consequent
            dummy_config = self.kcfg_explore.cterm_symbolic._definition.empty_config(sort=GENERATED_TOP_CELL)
            _result = self.kcfg_explore.cterm_symbolic.implies(
                antecedent=CTerm(config=dummy_config, constraints=[self.proof.simplified_antecedent]),
                consequent=CTerm(config=dummy_config, constraints=[self.proof.simplified_consequent]),
                bind_universally=self.proof.bind_universally,
            )
            result = _result.csubst
            if result is not None:
                self.proof.csubst = result

        _LOGGER.info(f'{proof_type} finished {self.proof.id}: {self.proof.status}')
