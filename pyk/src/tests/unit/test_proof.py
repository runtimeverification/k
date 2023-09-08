from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kcfg.kcfg import KCFG
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import intToken
from pyk.proof.equality import EqualityProof, EqualitySummary
from pyk.proof.proof import CompositeSummary, Proof, ProofStatus
from pyk.proof.reachability import APRBMCProof, APRBMCSummary, APRFailureInfo, APRProof, APRSummary

from .test_kcfg import node, node_dicts, term

if TYPE_CHECKING:
    from pathlib import Path

    from pytest import TempPathFactory


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


def apr_proof(i: int, proof_dir: Path) -> APRProof:
    return APRProof(
        id=f'apr_proof_{i}',
        kcfg=KCFG.from_dict({'nodes': node_dicts(i)}),
        terminal=[],
        init=node(1).id,
        target=node(1).id,
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
        terminal=[],
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
            terminal=[],
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof()

        # When
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict

    def test_read_proof_aprbmc(self, proof_dir: Path) -> None:
        sample_proof = APRBMCProof(
            id='aprbmc_proof_1',
            bmc_depth=1,
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            terminal=[],
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof()

        # When
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=proof_dir)

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
        proof_from_disk = Proof.read_proof(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict


#### APRProof


def test_read_write_proof_data(proof_dir: Path) -> None:
    kcfg = KCFG(proof_dir / 'apr_proof_1' / 'kcfg')
    node1 = kcfg.create_node(term(1))
    node2 = kcfg.create_node(term(2))
    kcfg.create_node(term(3))
    kcfg.create_node(term(4))

    proof = APRProof(
        id='apr_proof_1',
        kcfg=kcfg,
        terminal=[],
        init=node1.id,
        target=node2.id,
        logs={},
        proof_dir=proof_dir,
    )

    proof.write_proof_data()

    proof_from_disk = APRProof.read_proof_data(id=proof.id, proof_dir=proof_dir)

    assert proof_from_disk.dict == proof.dict


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
    eq_proof.write_proof_data()
    proof.read_subproof_data(eq_proof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir, proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_nested_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof.proof_dir, proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    sub_proof_1 = equality_proof(1, proof_dir)
    sub_proof_2 = apr_proof(2, proof_dir)
    sub_proof_3 = aprbmc_proof(3, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    sub_proof_1.write_proof_data()
    sub_proof_2.write_proof_data()
    sub_proof_3.write_proof_data()
    proof.read_subproof_data(sub_proof_1.id)
    proof.read_subproof_data(sub_proof_2.id)
    proof.read_subproof_data(sub_proof_3.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof.proof_dir, proof.id)

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
    eq_proof.write_proof_data()
    proof.read_subproof_data(eq_proof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof.proof_dir, proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = aprbmc_proof(1, proof_dir)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof.proof_dir, proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_print_failure_info() -> None:
    failing_nodes = [3, 5]
    pending_nodes = [6, 7, 8]

    path_conditions = {}
    path_conditions[3] = 'true #Equals X <=Int 100'
    path_conditions[5] = '#Top'

    failure_reasons = {}
    failure_reasons[
        3
    ] = 'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\nSTATE_CELL: $n |-> 2 #Implies 1'
    failure_reasons[
        5
    ] = 'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\nSTATE_CELL: $n |-> 5 #Implies 6'

    models: dict[int, list[tuple[str, str]]] = {}
    models[5] = [('X', '101')]

    failure_info = APRFailureInfo(
        failing_nodes=failing_nodes,
        pending_nodes=pending_nodes,
        failure_reasons=failure_reasons,
        path_conditions=path_conditions,
        models=models,
    )

    actual_output = '\n'.join(failure_info.print())
    expected_output = r"""5 Failure nodes. (3 pending and 2 failing)

Pending nodes: [6, 7, 8]

Failing nodes:

  Node id: 3
  Failure reason:
    Structural matching failed, the following cells failed individually (antecedent #Implies consequent):
    STATE_CELL: $n |-> 2 #Implies 1
  Path condition:
    true #Equals X <=Int 100
  Failed to generate a model.

  Node id: 5
  Failure reason:
    Structural matching failed, the following cells failed individually (antecedent #Implies consequent):
    STATE_CELL: $n |-> 5 #Implies 6
  Path condition:
    #Top
  Model:
    X = 101

Join the Runtime Verification Discord server for support: https://discord.gg/CurfmXNtbN"""

    assert actual_output == expected_output


def test_apr_proof_summary(proof_dir: Path) -> None:
    proof = apr_proof(1, proof_dir)

    assert len(proof.summary.summaries) == 1
    assert proof.summary == CompositeSummary(
        [
            APRSummary(
                id='apr_proof_1',
                status=ProofStatus.PASSED,
                admitted=False,
                nodes=1,
                pending=0,
                failing=0,
                vacuous=0,
                stuck=0,
                terminal=0,
                refuted=0,
                subproofs=0,
            )
        ]
    )


def test_aprbmc_proof_summary(proof_dir: Path) -> None:
    proof = aprbmc_proof(1, proof_dir)

    assert len(proof.summary.summaries) == 1
    assert proof.summary == CompositeSummary(
        [
            APRBMCSummary(
                id='aprbmc_proof_1',
                status=ProofStatus.PASSED,
                bmc_depth=1,
                nodes=1,
                pending=0,
                failing=0,
                vacuous=0,
                stuck=0,
                terminal=0,
                refuted=0,
                subproofs=0,
                bounded=0,
            )
        ]
    )


def test_apr_proof_summary_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof.proof_dir, proof.id)

    # Then
    comp_summary = proof_from_disk.summary
    assert isinstance(comp_summary, CompositeSummary)
    assert len(comp_summary.summaries) == 2
    assert comp_summary.summaries[0] == APRSummary(
        id='apr_proof_1',
        status=ProofStatus.PENDING,
        admitted=False,
        nodes=1,
        pending=0,
        failing=0,
        vacuous=0,
        stuck=0,
        terminal=0,
        refuted=0,
        subproofs=1,
    )

    assert comp_summary.summaries[1] == CompositeSummary(
        [
            APRSummary(
                id='apr_proof_2',
                status=ProofStatus.PENDING,
                admitted=False,
                nodes=2,
                pending=1,
                failing=0,
                vacuous=0,
                stuck=0,
                terminal=0,
                refuted=0,
                subproofs=1,
            ),
            EqualitySummary(
                id='equality_proof_1',
                status=ProofStatus.PENDING,
                admitted=False,
            ),
        ]
    )
