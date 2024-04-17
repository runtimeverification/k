from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KToken
from pyk.prelude.kbool import BOOL
from pyk.prelude.ml import mlAnd, mlEqualsTrue
from pyk.proof import EqualityProof, ImpliesProof, ImpliesProver, ProofStatus
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprint import SymbolTable
    from pyk.ktool.kprove import KProve


_LOGGER: Final = logging.getLogger(__name__)

FAILING_TESTS = ('func-spec-symbolic-add-comm',)

IMPLIES_PROOF_TEST_DATA: Iterable[tuple[str, tuple[str, ...], tuple[str, ...], bool, ProofStatus]] = (
    (
        'antecedent-bottom',
        ('X <=Int 0', '0 <Int X'),
        ('X <Int 3',),
        True,
        ProofStatus.PASSED,
    ),
    (
        'consequent-top',
        ('X <Int 3',),
        ('X <Int X +Int 1',),
        True,
        ProofStatus.PASSED,
    ),
    (
        'satisfiable-not-valid',
        ('X <Int 3',),
        ('X <Int 2',),
        True,
        ProofStatus.FAILED,
    ),
    (
        'satisfiable-not-valid-true-antecedent',
        (),
        ('X <=Int 0',),
        True,
        ProofStatus.FAILED,
    ),
    (
        'satisfiable-not-valid-existential',
        (),
        ('X <=Int 0',),
        False,
        ProofStatus.PASSED,
    ),
)


FUNC_PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, ProofStatus]] = (
    (
        'func-spec-concrete',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-addition',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-fail',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-addition-fail',
        ProofStatus.FAILED,
    ),
    (
        'func-spec-concrete-identity',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-identity',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-nonsense',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-nonsense',
        ProofStatus.FAILED,
    ),
    (
        'func-spec-concrete-requires-trivial-false-identity',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-requires-trivial-false-identity',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-requires-nontrivial-false-identity',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-requires-nontrivial-false-identity',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-requires-trivial-false-nonsense',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-requires-trivial-false-nonsense',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-requires-trivial-false-nonsense-undecided',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-requires-trivial-false-nonsense-undecided',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-requires-nontrivial-false-nonsense-undecided',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-requires-trivial-false-nonsense-undecided',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-concrete-requires-nontrivial-false-nonsense',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'concrete-requires-nontrivial-false-nonsense',
        ProofStatus.PASSED,
    ),
    (
        'func-spec-symbolic-add-comm',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'symbolic-addition-commutativity',
        ProofStatus.PASSED,
    ),
    (
        'ite-sort-param',
        K_FILES / 'imp-simple-spec.k',
        'IMP-FUNCTIONAL-SPEC',
        'ite-sort-param',
        ProofStatus.PASSED,
    ),
)


class TestImpImpliesProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp-verification.k'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['.List{"_,_"}_Ids'] = lambda: '.Ids'

    @pytest.mark.parametrize(
        'test_id,antecedents,consequents,bind_universally,expected_proof_status',
        IMPLIES_PROOF_TEST_DATA,
        ids=[test_id for test_id, *_ in IMPLIES_PROOF_TEST_DATA],
    )
    def test_implies_proof(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        antecedents: Iterable[str],
        consequents: Iterable[str],
        bind_universally: bool,
        expected_proof_status: ProofStatus,
    ) -> None:
        if test_id in FAILING_TESTS:
            pytest.skip()

        parsed_antecedents = [kprove.parse_token(KToken(antecedent, BOOL), as_rule=True) for antecedent in antecedents]
        parsed_consequents = [kprove.parse_token(KToken(consequent, BOOL), as_rule=True) for consequent in consequents]
        antecedent = mlAnd(mlEqualsTrue(pa) for pa in parsed_antecedents)
        consequent = mlAnd(mlEqualsTrue(pc) for pc in parsed_consequents)

        proof = ImpliesProof(test_id, antecedent, consequent, bind_universally=bind_universally)
        prover = ImpliesProver(proof, kcfg_explore)

        prover.advance_proof(proof)

        assert proof.status == expected_proof_status

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id, proof_status',
        FUNC_PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in FUNC_PROVE_TEST_DATA],
    )
    def test_functional_prove(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: Path,
        spec_module: str,
        claim_id: str,
        proof_status: ProofStatus,
    ) -> None:
        if test_id in FAILING_TESTS:
            pytest.skip()

        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        equality_proof = EqualityProof.from_claim(claim, kprove.definition)
        equality_prover = ImpliesProver(equality_proof, kcfg_explore)
        equality_prover.advance_proof(equality_proof)

        assert equality_proof.status == proof_status
