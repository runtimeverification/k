from __future__ import annotations

from threading import Event
from typing import TYPE_CHECKING

from pyk.proof.proof import Proof, ProofStatus, Prover

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path
    from typing import Any


class _StepInterrupted(Exception):
    """Raised inside `step_proof` when the prover is interrupted, mimicking a backend abort."""


class CountingProof(Proof[int, int]):
    """Minimal proof that needs `target` committed steps to pass."""

    target: int
    committed: int

    def __init__(self, id: str, target: int) -> None:
        super().__init__(id)
        self.target = target
        self.committed = 0

    def commit(self, result: int) -> None:
        self.committed += result

    @property
    def own_status(self) -> ProofStatus:
        return ProofStatus.PASSED if self.committed >= self.target else ProofStatus.PENDING

    @property
    def can_progress(self) -> bool:
        return self.committed < self.target

    @classmethod
    def from_dict(cls: type[CountingProof], dct: Mapping[str, Any], proof_dir: Path | None = None) -> CountingProof:
        raise NotImplementedError

    def write_proof_data(self) -> None: ...

    def get_steps(self) -> list[int]:
        return [self.committed] if self.can_progress else []


class CountingProver(Prover[CountingProof, int, int]):
    """Prover whose `step_proof` is "slow" (blocks for up to `slow_step_secs`) while `depth` exceeds `quick_at_depth`.

    Mirrors `APRProver`: a fixed `step_timeout` budgets each step, and `shrink_step` halves the depth.
    A slow step that is interrupted before its budget elapses raises (mimicking a backend abort); a slow
    step that is never interrupted finishes its work on its own. Tracks the number of interruptions so
    tests can assert how many times a step was shrunk.
    """

    depth: int
    quick_at_depth: int
    step_timeout: int | None
    slow_step_secs: float
    interrupt_count: int
    _interrupt_event: Event

    def __init__(
        self, depth: int, quick_at_depth: int, step_timeout: int | None = 1, slow_step_secs: float = 10.0
    ) -> None:
        self.depth = depth
        self.quick_at_depth = quick_at_depth
        self.step_timeout = step_timeout
        self.slow_step_secs = slow_step_secs
        self.interrupt_count = 0
        self._interrupt_event = Event()

    def close(self) -> None: ...

    def failure_info(self, proof: CountingProof) -> Any:
        return None

    def init_proof(self, proof: CountingProof) -> None: ...

    def shrink_step(self) -> bool:
        if self.depth <= 1:
            return False
        self.depth = max(1, self.depth // 2)
        return True

    def interrupt(self) -> None:
        self.interrupt_count += 1
        self._interrupt_event.set()

    def step_proof(self, step: int) -> list[int]:
        self._interrupt_event.clear()
        if self.depth > self.quick_at_depth:
            # A "slow" step: block for up to `slow_step_secs`. If `advance_proof` interrupts us first
            # (because the step budget elapsed) abort like a real backend; otherwise the step finishes
            # its work on its own and commits normally.
            if self._interrupt_event.wait(timeout=self.slow_step_secs):
                raise _StepInterrupted()
        return [1]


def test_advance_proof_shrinks_until_progress() -> None:
    # Given: depth 4 stalls, but a step completes once depth drops to <= 2.
    proof = CountingProof('counting', target=1)
    prover = CountingProver(depth=4, quick_at_depth=2)

    # When
    prover.advance_proof(proof)

    # Then: one timeout shrinks 4 -> 2, then a step commits and the proof passes.
    assert proof.status == ProofStatus.PASSED
    assert prover.depth == 2
    assert prover.interrupt_count == 1


def test_advance_proof_stops_when_cannot_shrink_further() -> None:
    # Given: every step stalls regardless of depth.
    proof = CountingProof('counting', target=1)
    prover = CountingProver(depth=2, quick_at_depth=0)

    # When
    prover.advance_proof(proof)

    # Then: depth shrinks 2 -> 1, then stops at the floor; the proof stays pending.
    assert proof.status == ProofStatus.PENDING
    assert proof.committed == 0
    assert prover.depth == 1
    assert prover.interrupt_count == 2


def test_advance_proof_no_shrink_when_steps_are_fast() -> None:
    # Given: step_timeout set but steps always complete in time.
    proof = CountingProof('counting', target=3)
    prover = CountingProver(depth=2, quick_at_depth=2)

    # When
    prover.advance_proof(proof)

    # Then: no interruptions, depth untouched, proof passes.
    assert proof.status == ProofStatus.PASSED
    assert prover.depth == 2
    assert prover.interrupt_count == 0


def test_advance_proof_without_step_timeout_is_unaffected() -> None:
    # Given: step_timeout is None -> classic in-loop behavior, no watchdog thread. Each step is "slow"
    # (depth 8 > quick_at_depth 4), but without a budget nothing interrupts it, so the step runs to
    # completion synchronously instead of being aborted and shrunk.
    proof = CountingProof('counting', target=2)
    prover = CountingProver(depth=8, quick_at_depth=4, step_timeout=None, slow_step_secs=0.05)

    # When
    prover.advance_proof(proof)

    # Then: both slow steps complete on their own; nothing is interrupted or shrunk.
    assert proof.status == ProofStatus.PASSED
    assert prover.depth == 8
    assert prover.interrupt_count == 0
