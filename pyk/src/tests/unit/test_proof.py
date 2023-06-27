from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kcfg.kcfg import KCFG
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import intToken
from pyk.proof.equality import EqualityProof
from pyk.proof.proof import Proof
from pyk.proof.reachability import APRBMCProof, APRProof

from .test_kcfg import node, node_dicts

if TYPE_CHECKING:
    from pathlib import Path

    from pytest import TempPathFactory


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


def apr_proof(i: int, proof_dir: Path) -> APRProof:
    return APRProof(
        id=f'apr_proof_{i}',
        init=node(1).id,
        target=node(1).id,
        kcfg=KCFG.from_dict({'nodes': node_dicts(i)}),
        logs={},
        proof_dir=proof_dir,
    )


def aprbmc_proof(i: int, proof_dir: Path) -> APRBMCProof:
    return APRBMCProof(
        id=f'aprbmc_proof_{i}',
        init=node(1).id,
        target=node(1).id,
        bmc_depth=i,
        kcfg=KCFG.from_dict({'nodes': node_dicts(i)}),
        logs={},
        proof_dir=proof_dir,
    )


def equality_proof(i: int, proof_dir: Path) -> EqualityProof:
    return EqualityProof(
        id=f'equality_proof_{i}', lhs_body=intToken(i), rhs_body=intToken(i), sort=BOOL, proof_dir=proof_dir
    )


class TestProof:
    def test_read_proof_apr(self, proof_dir: Path) -> None:
        sample_proof = APRProof(
            id='apr_proof_1',
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof()

        # When
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=sample_proof.proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict

    def test_read_proof_aprbmc(self, proof_dir: Path) -> None:
        sample_proof = APRBMCProof(
            id='aprbmc_proof_1',
            bmc_depth=1,
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof()

        # When
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=sample_proof.proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict

    def test_read_proof_equality(self, proof_dir: Path) -> None:
        sample_proof = EqualityProof(
            id='equality_proof_1',
            lhs_body=intToken(1),
            rhs_body=intToken(1),
            sort=BOOL,
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof()

        # When
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=sample_proof.proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict


#### APRProof


def test_apr_proof_from_dict_no_subproofs(proof_dir: Path) -> None:
    # Given
    proof = apr_proof(1, proof_dir)

    # When
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_one_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof()
    proof.read_subproof(eq_proof.id)
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_nested_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof()
    subproof.read_subproof(eq_proof.id)
    subproof.write_proof()
    proof.read_subproof(subproof.id)
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    sub_proof_1 = equality_proof(1, proof_dir)
    sub_proof_2 = apr_proof(2, proof_dir)
    sub_proof_3 = aprbmc_proof(3, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    sub_proof_1.write_proof()
    sub_proof_2.write_proof()
    sub_proof_3.write_proof()
    proof.read_subproof(sub_proof_1.id)
    proof.read_subproof(sub_proof_2.id)
    proof.read_subproof(sub_proof_3.id)
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


#### APRBMCProof


def test_aprbmc_proof_from_dict_no_subproofs(proof_dir: Path) -> None:
    # Given
    proof = aprbmc_proof(1, proof_dir)

    # When
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_one_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    proof = aprbmc_proof(1, proof_dir)

    # When
    eq_proof.write_proof()
    proof.read_subproof(eq_proof.id)
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = aprbmc_proof(1, proof_dir)

    # When
    eq_proof.write_proof()
    subproof.read_subproof(eq_proof.id)
    subproof.write_proof()
    proof.read_subproof(subproof.id)
    proof.write_proof()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof(proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict
