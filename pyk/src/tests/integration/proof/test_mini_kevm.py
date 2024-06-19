from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KVariable
from pyk.kcfg.show import KCFGShow
from pyk.prelude.kint import INT, intToken, leInt, ltInt
from pyk.prelude.ml import mlEquals, mlEqualsTrue, mlNot
from pyk.proof import APRProof, APRProver, ProofStatus
from pyk.proof.show import APRProofNodePrinter
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final, Union

    from pytest import TempPathFactory

    from pyk.cterm.symbolic import CTermSymbolic
    from pyk.kast.inner import KInner
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprove import KProve

    STATE = Union[tuple[str, str], tuple[str, str, str]]

_LOGGER: Final = logging.getLogger(__name__)


def int_var(var: str) -> KInner:
    return KVariable(var, sort=INT)


def eq_int(var: str, val: int) -> KInner:
    return mlEquals(int_var(var), intToken(val), arg_sort=INT)


def ne_int(var: str, val: int) -> KInner:
    return mlNot(eq_int(var, val))


def plus_int(a: KInner, b: KInner) -> KInner:
    return KApply('_+Int_', a, b)


APR_PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None, Iterable[str], ProofStatus, int]] = (
    (
        'ensures-constraint-simplification',
        K_FILES / 'mini-kevm-spec.k',
        'MINI-KEVM-SPEC',
        'ensures-constraint',
        2,
        1,
        [],
        ProofStatus.PASSED,
        1,
    ),
)

NORMALIZE_DNF_TEST_DATA = [
    (
        'simple',
        [
            [
                mlEqualsTrue(ltInt(int_var('X'), intToken(7))),
                mlEqualsTrue(ltInt(int_var('T'), plus_int(int_var('CONTRACT_ID'), intToken(4)))),
                eq_int('CALLER_ID', 4),
            ],
            [
                mlEqualsTrue(ltInt(int_var('X'), plus_int(int_var('CALLER_ID'), intToken(3)))),
                ne_int('CALLER_ID', 4),
            ],
            [
                mlEqualsTrue(leInt(plus_int(int_var('CONTRACT_ID'), intToken(4)), int_var('T'))),
                eq_int('CALLER_ID', 4),
            ],
        ],
        [
            mlEqualsTrue(ltInt(intToken(0), int_var('X'))),
            mlEqualsTrue(ltInt(intToken(0), int_var('Y'))),
            mlEqualsTrue(ltInt(intToken(0), int_var('Z'))),
            mlEqualsTrue(ltInt(int_var('T'), plus_int(int_var('CALLER_ID'), int_var('CONTRACT_ID')))),
        ],
        [
            [
                mlEqualsTrue(ltInt(int_var('X'), plus_int(int_var('CALLER_ID'), intToken(3)))),
                eq_int('CALLER_ID', 4),
            ],
            [
                mlEqualsTrue(ltInt(int_var('X'), plus_int(int_var('CALLER_ID'), intToken(3)))),
                ne_int('CALLER_ID', 4),
            ],
        ],
    ),
]


def leaf_number(proof: APRProof) -> int:
    non_target_leaves = [nd for nd in proof.kcfg.leaves if not proof.is_target(nd.id)]
    return len(non_target_leaves) + len(proof.kcfg.predecessors(proof.target))


class TestMiniKEVM(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'mini-kevm.k'
    # Disabled until resolved: https://github.com/runtimeverification/haskell-backend/issues/3761
    DISABLE_LEGACY = True

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth,cut_rules,proof_status,expected_leaf_number',
        APR_PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in APR_PROVE_TEST_DATA],
    )
    def test_all_path_reachability_prove(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        max_iterations: int | None,
        max_depth: int | None,
        cut_rules: Iterable[str],
        proof_status: ProofStatus,
        expected_leaf_number: int,
        tmp_path_factory: TempPathFactory,
    ) -> None:
        with tmp_path_factory.mktemp('apr_tmp_proofs') as proof_dir:
            claim = single(
                kprove.get_claims(
                    Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}']
                )
            )
            proof = APRProof.from_claim(kprove.definition, claim, logs={}, proof_dir=proof_dir)

            new_init_cterm = kcfg_explore.cterm_symbolic.assume_defined(proof.kcfg.node(proof.init).cterm)
            proof.kcfg.let_node(proof.init, cterm=new_init_cterm)
            kcfg_explore.simplify(proof.kcfg, {})

            prover = APRProver(
                kcfg_explore=kcfg_explore,
                execute_depth=max_depth,
                cut_point_rules=cut_rules,
            )
            prover.advance_proof(proof, max_iterations=max_iterations)

            kcfg_show = KCFGShow(
                kprove, node_printer=APRProofNodePrinter(proof, kprove, full_printer=True, minimize=False)
            )
            cfg_lines = kcfg_show.show(proof.kcfg)
            _LOGGER.info('\n'.join(cfg_lines))

            assert proof.status == proof_status
            assert leaf_number(proof) == expected_leaf_number

    @pytest.mark.parametrize(
        'test_id,dnf,path_condition,expected',
        NORMALIZE_DNF_TEST_DATA,
        ids=[test_id for test_id, *_ in NORMALIZE_DNF_TEST_DATA],
    )
    def test_normalize_dnf(
        self,
        cterm_symbolic: CTermSymbolic,
        test_id: str,
        dnf: list[list[KInner]],
        path_condition: list[KInner],
        expected: list[list[KInner]],
    ) -> None:
        assert cterm_symbolic.normalize_dnf(dnf, path_condition) == []
