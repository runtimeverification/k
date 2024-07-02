from __future__ import annotations

from typing import TYPE_CHECKING

from . import convert

if TYPE_CHECKING:
    from ..kore.syntax import Axiom, Pattern


def get_requires(axiom: Axiom) -> Pattern | None:
    llvm_axiom = convert.sentence_to_llvm(axiom)
    llvm_pattern = llvm_axiom.requires
    if llvm_pattern is None:
        return None
    return convert.llvm_to_pattern(llvm_pattern)
