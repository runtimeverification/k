from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..kast.manip import extract_lhs
from ..kast.outer import KApply
from ..proof import APRProof, APRProver, EqualityProof, ImpliesProver

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path
    from typing import ContextManager, Final

    from ..cli.pyk import ProveOptions
    from ..kast.outer import KClaim
    from ..kcfg import KCFGExplore
    from ..proof import Proof, Prover
    from .kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)


class ProveRpc:
    _kprove: KProve
    _explore_context: Callable[[], ContextManager[KCFGExplore]]

    def __init__(
        self,
        kprove: KProve,
        explore_context: Callable[[], ContextManager[KCFGExplore]],
    ):
        self._kprove = kprove
        self._explore_context = explore_context

    def prove_rpc(self, options: ProveOptions) -> list[Proof]:
        all_claims = self._kprove.get_claims(
            options.spec_file,
            spec_module_name=options.spec_module,
            claim_labels=options.claim_labels,
            exclude_claim_labels=options.exclude_claim_labels,
            type_inference_mode=options.type_inference_mode,
        )

        if all_claims is None:
            raise ValueError(f'No claims found in file: {options.spec_file}')

        return [
            self._prove_claim_rpc(
                claim,
                max_depth=options.max_depth,
                save_directory=options.save_directory,
                max_iterations=options.max_iterations,
            )
            for claim in all_claims
        ]

    def _prove_claim_rpc(
        self,
        claim: KClaim,
        max_depth: int | None = None,
        save_directory: Path | None = None,
        max_iterations: int | None = None,
    ) -> Proof:
        definition = self._kprove.definition

        proof: Proof
        prover: Prover
        lhs_top = extract_lhs(claim.body)
        is_functional_claim = type(lhs_top) is KApply and definition.symbols[lhs_top.label.name] in definition.functions

        if is_functional_claim:
            proof = EqualityProof.from_claim(claim, definition, proof_dir=save_directory)
            if save_directory is not None and EqualityProof.proof_data_exists(proof.id, save_directory):
                _LOGGER.info(f'Reloading from disk {proof.id}: {save_directory}')
                proof = EqualityProof.read_proof_data(save_directory, proof.id)

        else:
            proof = APRProof.from_claim(definition, claim, {}, proof_dir=save_directory)
            if save_directory is not None and APRProof.proof_data_exists(proof.id, save_directory):
                _LOGGER.info(f'Reloading from disk {proof.id}: {save_directory}')
                proof = APRProof.read_proof_data(save_directory, proof.id)

        if not proof.passed and (max_iterations is None or max_iterations > 0):
            with self._explore_context() as kcfg_explore:
                if is_functional_claim:
                    assert type(proof) is EqualityProof
                    prover = ImpliesProver(proof, kcfg_explore)
                else:
                    assert type(proof) is APRProof
                    prover = APRProver(kcfg_explore, execute_depth=max_depth)
                prover.advance_proof(proof, max_iterations=max_iterations)

        if proof.passed:
            _LOGGER.info(f'Proof passed: {proof.id}')
        elif proof.failed:
            _LOGGER.info(f'Proof failed: {proof.id}')
        else:
            _LOGGER.info(f'Proof pending: {proof.id}')
        return proof
