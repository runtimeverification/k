from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kcfg.kcfg import KCFG
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import intToken
from pyk.proof.equality import EqualityProof
from pyk.proof.proof import Proof
from pyk.proof.reachability import APRBMCProof, APRProof

from .test_kcfg import node_dicts

if TYPE_CHECKING:
    from pathlib import Path

    from pytest import FixtureRequest, TempPathFactory


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


PROOF_TEST_DATA: list[tuple[str, str, Proof]] = [
    (
        'apr-proof',
        'proof_dir',
        APRProof(
            id='apr_proof_1',
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            logs={},
        ),
    ),
    (
        'aprbmc-proof',
        'proof_dir',
        APRBMCProof(
            id='aprbmc_proof_1',
            bmc_depth=1,
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            logs={},
        ),
    ),
    (
        'equality-proof',
        'proof_dir',
        EqualityProof(
            id='equality_proof_1',
            lhs_body=intToken(1),
            rhs_body=intToken(1),
            sort=BOOL,
        ),
    ),
]


class TestProof:
    @pytest.mark.parametrize(
        'test_id,dir_fixture,sample_proof',
        PROOF_TEST_DATA,
        ids=[test_id for test_id, *_ in PROOF_TEST_DATA],
    )
    def test_read_proof(self, request: FixtureRequest, test_id: str, dir_fixture: str, sample_proof: Proof) -> None:
        sample_proof.proof_dir = request.getfixturevalue(dir_fixture)

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof()

        # When
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=sample_proof.proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict
