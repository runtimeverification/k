from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from pyk.kast.inner import KApply, KSequence
from pyk.kcfg.semantics import DefaultSemantics
from pyk.proof import APRProof, APRProver
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from typing import Final

    from pyk.cterm import CTerm
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import KCFGExtendResult
    from pyk.kcfg.semantics import KCFGSemantics
    from pyk.ktool.kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)


class SimpleSemantics(DefaultSemantics):
    def is_terminal(self, c: CTerm) -> bool:
        k_cell = c.cell('K_CELL')
        if type(k_cell) is KSequence and type(k_cell[0]) is KApply and k_cell[0].label.name == 'f_SIMPLE-PROOFS_Step':
            return True
        return False

    def abstract_node(self, c: CTerm) -> CTerm:
        return c

    def same_loop(self, c1: CTerm, c2: CTerm) -> bool:
        return False

    def custom_step(self, c: CTerm) -> KCFGExtendResult | None:
        return None


class TestSimpleProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'simple-proofs.k'
    KOMPILE_ARGS = {'syntax_module': 'SIMPLE-PROOFS'}
    LLVM_ARGS = {'syntax_module': 'SIMPLE-PROOFS'}

    def semantics(self, definition: KDefinition) -> KCFGSemantics:
        return SimpleSemantics()

    def test_terminal_node_marking(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
    ) -> None:
        spec_file = K_FILES / 'simple-proofs-spec.k'
        spec_module = 'SIMPLE-PROOFS-SPEC'

        claim = single(
            kprove.get_claims(spec_file, spec_module_name=spec_module, claim_labels=[f'{spec_module}.a-to-e'])
        )
        proof = APRProof.from_claim(kprove.definition, claim, logs={})
        kcfg_explore.simplify(proof.kcfg, {})
        prover = APRProver(
            kcfg_explore=kcfg_explore,
            execute_depth=1,
        )
        prover.advance_proof(proof)

        assert not proof.is_terminal(proof.target)
        for pred in proof.kcfg.predecessors(proof.target):
            assert not proof.is_terminal(pred.source.id)

        claim = single(
            kprove.get_claims(spec_file, spec_module_name=spec_module, claim_labels=[f'{spec_module}.a-to-f'])
        )
        proof = APRProof.from_claim(kprove.definition, claim, logs={})
        kcfg_explore.simplify(proof.kcfg, {})
        prover = APRProver(
            kcfg_explore=kcfg_explore,
            execute_depth=1,
        )
        prover.advance_proof(proof)

        assert proof.is_terminal(proof.target)
        for pred in proof.kcfg.predecessors(proof.target):
            assert proof.is_terminal(pred.source.id)
