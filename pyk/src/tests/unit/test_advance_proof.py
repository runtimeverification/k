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
    """Prover whose `step_proof` stalls (blocks until interrupted) while `depth` exceeds `quick_at_depth`.

    Tracks the number of interruptions so tests can assert how many times the depth was halved.
    """

    depth: int
    quick_at_depth: int
    interrupt_count: int
    _interrupt_event: Event

    def __init__(self, depth: int, quick_at_depth: int) -> None:
        self.depth = depth
        self.quick_at_depth = quick_at_depth
        self.interrupt_count = 0
        self._interrupt_event = Event()

    def close(self) -> None: ...

    def failure_info(self, proof: CountingProof) -> Any:
        return None

    def init_proof(self, proof: CountingProof) -> None: ...

    def get_step_depth(self) -> int | None:
        return self.depth

    def set_step_depth(self, depth: int) -> None:
        self.depth = depth

    def interrupt(self) -> None:
        self.interrupt_count += 1
        self._interrupt_event.set()

    def step_proof(self, step: int) -> list[int]:
        self._interrupt_event.clear()
        if self.depth > self.quick_at_depth:
            # Stall until `advance_proof` interrupts us once the stall window elapses.
            if self._interrupt_event.wait(timeout=10.0):
                raise _StepInterrupted()
            raise AssertionError('step_proof was not interrupted within 10s')
        return [1]


PER_DEPTH_TIMEOUT = 0.02


def test_advance_proof_halves_depth_until_progress() -> None:
    # Given: depth 8 stalls, but a step completes once depth drops to <= 2.
    proof = CountingProof('counting', target=1)
    prover = CountingProver(depth=8, quick_at_depth=2)

    # When
    prover.advance_proof(proof, per_depth_timeout=PER_DEPTH_TIMEOUT)

    # Then: 8 -> 4 -> 2 (two halvings, two interrupts), then a step commits and the proof passes.
    assert proof.status == ProofStatus.PASSED
    assert prover.depth == 2
    assert prover.interrupt_count == 2


def test_advance_proof_stops_at_minimum_depth_when_never_progressing() -> None:
    # Given: every step stalls regardless of depth.
    proof = CountingProof('counting', target=1)
    prover = CountingProver(depth=4, quick_at_depth=0)

    # When
    prover.advance_proof(proof, per_depth_timeout=PER_DEPTH_TIMEOUT)

    # Then: depth halves 4 -> 2 -> 1, then stops at the floor; the proof stays pending.
    assert proof.status == ProofStatus.PENDING
    assert proof.committed == 0
    assert prover.depth == 1
    assert prover.interrupt_count == 3


def test_advance_proof_no_halving_when_steps_are_fast() -> None:
    # Given: progressive policy enabled but steps always complete in time.
    proof = CountingProof('counting', target=3)
    prover = CountingProver(depth=8, quick_at_depth=8)

    # When
    prover.advance_proof(proof, per_depth_timeout=PER_DEPTH_TIMEOUT)

    # Then: no interruptions, depth untouched, proof passes.
    assert proof.status == ProofStatus.PASSED
    assert prover.depth == 8
    assert prover.interrupt_count == 0


def test_advance_proof_without_per_depth_timeout_is_unaffected() -> None:
    # Given: no per_depth_timeout -> classic in-loop behavior, no watchdog thread.
    proof = CountingProof('counting', target=2)
    prover = CountingProver(depth=8, quick_at_depth=8)

    # When
    prover.advance_proof(proof)

    # Then
    assert proof.status == ProofStatus.PASSED
    assert prover.depth == 8
    assert prover.interrupt_count == 0
