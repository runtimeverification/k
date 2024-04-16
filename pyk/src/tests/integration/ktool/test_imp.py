from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cli.pyk import ProveOptions
from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.kcfg.semantics import KCFGSemantics
from pyk.prelude.kbool import BOOL, notBool
from pyk.prelude.ml import mlEqualsTrue
from pyk.proof import ProofStatus
from pyk.testing import KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.cterm import CTerm
    from pyk.kast.inner import KInner
    from pyk.kast.outer import KDefinition
    from pyk.ktool.kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)


class ImpSemantics(KCFGSemantics):
    definition: KDefinition | None

    def __init__(self, definition: KDefinition | None = None):
        super().__init__()
        self.definition = definition

    def is_terminal(self, c: CTerm) -> bool:
        k_cell = c.cell('K_CELL')
        if type(k_cell) is KSequence:
            if len(k_cell) == 0:
                return True
            if len(k_cell) == 1 and type(k_cell[0]) is KVariable:
                return True
        if type(k_cell) is KVariable:
            return True
        return False

    def extract_branches(self, c: CTerm) -> list[KInner]:
        if self.definition is None:
            raise ValueError('IMP branch extraction requires a non-None definition')

        k_cell = c.cell('K_CELL')
        if type(k_cell) is KSequence and len(k_cell) > 0:
            k_cell = k_cell[0]
        if type(k_cell) is KApply and k_cell.label.name == 'if(_)_else_':
            condition = k_cell.args[0]
            if (type(condition) is KVariable and condition.sort == BOOL) or (
                type(condition) is KApply and self.definition.return_sort(condition.label) == BOOL
            ):
                return [mlEqualsTrue(condition), mlEqualsTrue(notBool(condition))]
        return []

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        k_cell_1 = c1.cell('K_CELL')
        k_cell_2 = c2.cell('K_CELL')
        if k_cell_1 == k_cell_2 and type(k_cell_1) is KSequence and type(k_cell_1[0]) is KApply:
            return k_cell_1[0].label.name == 'while(_)_'
        return False


PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, ProofStatus]] = (
    (
        'imp-simple-addition-1',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-1',
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-addition-2',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-2',
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-addition-var',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'addition-var',
        ProofStatus.PASSED,
    ),
    (
        'pre-branch-proved',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'pre-branch-proved',
        ProofStatus.PASSED,
    ),
    (
        'while-cut-rule',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'while-cut-rule',
        ProofStatus.PASSED,
    ),
    (
        'while-cut-rule-delayed',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'while-cut-rule-delayed',
        ProofStatus.PASSED,
    ),
    (
        'failing-if',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'failing-if',
        ProofStatus.FAILED,
    ),
    (
        'imp-simple-sum-10',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-10',
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-sum-100',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-100',
        ProofStatus.PASSED,
    ),
    (
        'imp-if-almost-same-plus',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC-DEPENDENCIES',
        'if-almost-same-plus',
        ProofStatus.PASSED,
    ),
    (
        'imp-if-almost-same-times',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'if-almost-same-times',
        ProofStatus.PASSED,
    ),
    (
        'imp-simple-sum-loop',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'sum-loop',
        ProofStatus.PASSED,
    ),
    (
        'imp-failing-circularity',
        K_FILES / 'imp-simple-spec.k',
        'IMP-SIMPLE-SPEC',
        'failing-circularity',
        ProofStatus.FAILED,
    ),
)


class TestImpProve(KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp-verification.k'

    def semantics(self, definition: KDefinition) -> KCFGSemantics:
        return ImpSemantics(definition)

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,proof_status',
        PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in PROVE_TEST_DATA],
    )
    def test_prove_rpc(
        self,
        kprove: KProve,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        proof_status: ProofStatus,
    ) -> None:
        proof = single(
            kprove.prove_rpc(
                ProveOptions(
                    {
                        'spec_file': Path(spec_file),
                        'spec_module': spec_module,
                        'claim_labels': [claim_id],
                    }
                ),
                kcfg_semantics=ImpSemantics(kprove.definition),
            )
        )
        assert proof.status == proof_status
