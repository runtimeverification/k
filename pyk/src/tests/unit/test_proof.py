from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kcfg.exploration import KCFGExplorationNodeAttr
from pyk.kcfg.kcfg import KCFG, KCFGNodeAttr
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import intToken
from pyk.proof import EqualityProof
from pyk.proof.implies import EqualitySummary
from pyk.proof.proof import CompositeSummary, Proof, ProofStatus
from pyk.proof.reachability import APRFailureInfo, APRProof, APRSummary

from .test_kcfg import minimization_test_kcfg, node, node_dicts, term

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pytest import TempPathFactory


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


def apr_proof(i: int, proof_dir: Path, bmc_depth: int | None = None) -> APRProof:
    return APRProof(
        id=f'apr_proof_{i}',
        kcfg=KCFG.from_dict({'nodes': node_dicts(i)}),
        terminal=[],
        init=node(1).id,
        target=node(1).id,
        logs={},
        proof_dir=proof_dir,
        bmc_depth=bmc_depth,
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
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert proof_from_disk.dict == sample_proof.dict

    def test_read_proof_with_attributes(self, proof_dir: Path) -> None:

        kcfg = KCFG.from_dict({'nodes': node_dicts(3)})
        kcfg.add_attr(1, KCFGNodeAttr.VACUOUS)
        kcfg.add_attr(2, KCFGExplorationNodeAttr.TERMINAL)
        sample_proof = APRProof(
            id='apr_proof_1',
            kcfg=kcfg,
            terminal=[],
            init=node(1).id,
            target=node(3).id,
            logs={},
            proof_dir=proof_dir,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

        # Then
        assert type(proof_from_disk) is type(sample_proof)
        assert type(proof_from_disk) is APRProof
        assert set(sample_proof.kcfg.nodes) == set(proof_from_disk.kcfg.nodes)

    def test_read_proof_aprbmc(self, proof_dir: Path) -> None:
        sample_proof = APRProof(
            id='aprbmc_proof_1',
            kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
            terminal=[],
            init=node(1).id,
            target=node(1).id,
            logs={},
            proof_dir=proof_dir,
            bmc_depth=1,
        )

        # Given
        assert sample_proof.proof_dir
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

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
        sample_proof.write_proof_data()

        # When
        proof_from_disk = Proof.read_proof_data(id=sample_proof.id, proof_dir=proof_dir)

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
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(id=proof.id, proof_dir=proof.proof_dir)

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
    proof_from_disk = Proof.read_proof_data(proof_dir=proof_dir, id=proof.id)

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
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    sub_proof_1 = equality_proof(1, proof_dir)
    sub_proof_2 = apr_proof(2, proof_dir)
    sub_proof_3 = apr_proof(3, proof_dir, bmc_depth=3)
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
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_apr_proof_minimization_and_terminals() -> None:
    #                                               25   /-- X >=Int 5 --> 10
    #     5    10    15    20   /-- X >=Int 0 --> 6 --> 8
    #  1 --> 2 --> 3 --> 4 --> 5                         \-- X  <Int 5 --> 11
    #              T            \                    30    35     40        T
    #                            \-- X  <Int 0 --> 7 --> 9 --> 12 --> 13
    #                                              T
    proof = APRProof(
        id='apr_min_proof',
        kcfg=minimization_test_kcfg(),
        terminal=[3, 9, 11],
        init=1,
        target=11,
        logs={},
    )

    assert proof.terminal_ids == {3, 9, 11}
    proof.minimize_kcfg()
    assert proof.terminal_ids == {11}


MODULE_NAME_TEST_DATA: Final = (
    ('sq-bracket', 'TEST-KONTROL-TEST-UINT256-BYTES[]-0', 'M-TEST-KONTROL-TEST-UINT256-BYTESbktbkt-0'),
    ('underscore', 'TEST_KONTROL_%)_UINT256-1', 'M-TEST-KONTROL-UINT256-1'),
)


@pytest.mark.parametrize(
    'test_id,proof_id,expected',
    MODULE_NAME_TEST_DATA,
    ids=[test_id for test_id, *_ in MODULE_NAME_TEST_DATA],
)
def test_proof_module_name(test_id: str, proof_id: str, expected: str) -> None:
    # Given
    output = APRProof._make_module_name(proof_id)

    # Then
    assert output == expected


#### APRBMCProof


def test_aprbmc_proof_from_dict_no_subproofs(proof_dir: Path) -> None:
    # Given
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    # When
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(id=proof.id, proof_dir=proof.proof_dir)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_one_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    # When
    eq_proof.write_proof_data()
    proof.read_subproof_data(eq_proof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_aprbmc_proof_from_dict_heterogeneous_subproofs(proof_dir: Path) -> None:
    # Given
    eq_proof = equality_proof(1, proof_dir)
    subproof = apr_proof(2, proof_dir)
    proof = apr_proof(1, proof_dir, bmc_depth=1)

    # When
    eq_proof.write_proof_data()
    subproof.read_subproof_data(eq_proof.id)
    subproof.write_proof_data()
    proof.read_subproof_data(subproof.id)
    proof.write_proof_data()
    assert proof.proof_dir
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

    # Then
    assert proof.dict == proof_from_disk.dict


def test_print_failure_info() -> None:
    failing_nodes = [3, 5]
    pending_nodes = [6, 7, 8]

    path_conditions = {}
    path_conditions[3] = 'true #Equals X <=Int 100'
    path_conditions[5] = '#Top'

    failure_reasons = {}
    failure_reasons[3] = (
        'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\nSTATE_CELL: $n |-> 2 #Implies 1'
    )
    failure_reasons[5] = (
        'Structural matching failed, the following cells failed individually (antecedent #Implies consequent):\nSTATE_CELL: $n |-> 5 #Implies 6'
    )

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
                bmc_depth=None,
                bounded=0,
                subproofs=0,
                formatted_exec_time='0s',
            )
        ]
    )


def test_aprbmc_proof_summary(proof_dir: Path) -> None:
    proof = apr_proof(1, proof_dir, bmc_depth=1)

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
                bmc_depth=1,
                bounded=0,
                subproofs=0,
                formatted_exec_time='0s',
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
    proof_from_disk = Proof.read_proof_data(proof_dir=proof.proof_dir, id=proof.id)

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
        bmc_depth=None,
        bounded=0,
        subproofs=1,
        formatted_exec_time='0s',
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
                bmc_depth=None,
                bounded=0,
                subproofs=1,
                formatted_exec_time='0s',
            ),
            EqualitySummary(
                id='equality_proof_1',
                status=ProofStatus.PENDING,
                admitted=False,
            ),
        ]
    )
