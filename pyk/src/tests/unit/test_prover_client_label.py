"""Auto-stamping of the kore-RPC `client_label` by APRProver / ImpliesProver.

Both provers call `cterm_symbolic.set_client_label(proof.id)` from `init_proof`
so booster's per-line `{request: ...}` context self-identifies the claim
without the consumer touching the API.
"""

from __future__ import annotations

from typing import TYPE_CHECKING
from unittest.mock import MagicMock

import pytest

from pyk.kast.prelude.kbool import BOOL
from pyk.kast.prelude.kint import intToken
from pyk.kcfg.kcfg import KCFG
from pyk.proof.implies import EqualityProof, ImpliesProver
from pyk.proof.reachability import APRProof, APRProver

from .test_kcfg import node, node_dicts

if TYPE_CHECKING:
    from pathlib import Path

    from pytest import TempPathFactory


@pytest.fixture(scope='function')
def proof_dir(tmp_path_factory: TempPathFactory) -> Path:
    return tmp_path_factory.mktemp('proofs')


def test_apr_prover_init_proof_stamps_client_label(proof_dir: Path) -> None:
    """APRProver.init_proof(proof) calls cterm_symbolic.set_client_label(proof.id) at the top."""
    kcfg_explore = MagicMock()
    # APRProver.__init__ reads kcfg_explore.cterm_symbolic._definition.main_module_name; pin it.
    kcfg_explore.cterm_symbolic._definition.main_module_name = 'TEST'
    # init_proof iterates [proof.init, proof.target] and calls is_terminal on each;
    # return False to avoid touching proof.add_terminal.
    kcfg_explore.kcfg_semantics.is_terminal.return_value = False

    prover = APRProver(kcfg_explore=kcfg_explore)
    proof = APRProof(
        id='apr_proof_1',
        kcfg=KCFG.from_dict({'nodes': node_dicts(1)}),
        terminal=[],
        init=node(1).id,
        target=node(1).id,
        logs={},
        proof_dir=proof_dir,
    )

    prover.init_proof(proof)

    kcfg_explore.cterm_symbolic.set_client_label.assert_called_once_with('apr_proof_1')


def test_implies_prover_init_proof_stamps_client_label(proof_dir: Path) -> None:
    """ImpliesProver.init_proof(proof) calls cterm_symbolic.set_client_label(proof.id)."""
    kcfg_explore = MagicMock()
    proof = EqualityProof(
        id='equality_proof_1', lhs_body=intToken(1), rhs_body=intToken(1), sort=BOOL, proof_dir=proof_dir
    )
    prover = ImpliesProver(proof, kcfg_explore=kcfg_explore)

    prover.init_proof(proof)

    kcfg_explore.cterm_symbolic.set_client_label.assert_called_once_with('equality_proof_1')
