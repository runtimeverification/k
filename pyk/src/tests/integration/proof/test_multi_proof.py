from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.proof import EqualityProof, ImpliesProver, ProofStatus
from pyk.proof.proof import MultiProof
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from typing import Final

    from pytest import TempPathFactory

    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprint import SymbolTable
    from pyk.ktool.kprove import KProve


_LOGGER: Final = logging.getLogger(__name__)


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


class TestImpMultiProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp-verification.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['.List{"_,_"}_Ids'] = lambda: '.Ids'

    MULTIPROOF_TEST_DATA = (
        ('multiproof-passing', 'concrete-addition', 'concrete-identity', ProofStatus.PASSED),
        ('multiproof-failing', 'concrete-addition-fail', 'concrete-identity', ProofStatus.FAILED),
    )

    @pytest.mark.parametrize(
        'test_id,claim_id_1,claim_id_2,proof_status',
        MULTIPROOF_TEST_DATA,
        ids=[test_id for test_id, *_ in MULTIPROOF_TEST_DATA],
    )
    def test_multiproof_pass(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        proof_dir: Path,
        test_id: str,
        claim_id_1: str,
        claim_id_2: str,
        proof_status: ProofStatus,
    ) -> None:

        spec_file = K_FILES / 'imp-simple-spec.k'
        spec_module = 'IMP-FUNCTIONAL-SPEC'

        claim_1 = single(
            kprove.get_claims(
                Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id_1}']
            )
        )
        claim_2 = single(
            kprove.get_claims(
                Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id_2}']
            )
        )

        equality_proof_1 = EqualityProof.from_claim(claim_1, kprove.definition, proof_dir=proof_dir)
        equality_proof_2 = EqualityProof.from_claim(claim_2, kprove.definition, proof_dir=proof_dir)

        equality_proof_1.write_proof_data()
        equality_proof_2.write_proof_data()

        mproof = MultiProof(
            id='multiproof1', subproof_ids=[equality_proof_1.id, equality_proof_2.id], proof_dir=proof_dir
        )

        assert mproof.status == ProofStatus.PENDING

        equality_prover = ImpliesProver(equality_proof_1, kcfg_explore)
        equality_prover.advance_proof(equality_proof_1)

        equality_prover = ImpliesProver(equality_proof_2, kcfg_explore)
        equality_prover.advance_proof(equality_proof_2)

        assert mproof.status == proof_status
