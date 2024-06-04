from __future__ import annotations

from typing import TYPE_CHECKING

import pykframework.kllvm.load  # noqa: F401
from pykframework.kllvm.parser import Parser
from pykframework.testing import RuntimeTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pykframework.kllvm.ast import Pattern
    from pykframework.kllvm.runtime import Runtime


class TestInternalTerm(RuntimeTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    def test_str_llvm_backend_issue_724(self, runtime: Runtime) -> None:
        for _ in range(10000):
            term = runtime._module.InternalTerm(start_pattern())
            term.step(-1)
            # just checking that str doesn't crash
            str(term)


def start_pattern() -> Pattern:
    """
    <k> int x ; x = 1 </k>
    """
    text = r"""
        LblinitGeneratedTopCell{}(
            Lbl'Unds'Map'Unds'{}(
                Lbl'Stop'Map{}(),
                Lbl'UndsPipe'-'-GT-Unds'{}(
                    inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$PGM")),
                    inj{SortPgm{}, SortKItem{}}(
                        Lblint'UndsSClnUnds'{}(
                            Lbl'UndsCommUnds'{}(
                                \dv{SortId{}}("x"),
                                Lbl'Stop'List'LBraQuotUndsCommUndsQuotRBra'{}()
                            ),
                            Lbl'UndsEqlsUndsSCln'{}(
                                \dv{SortId{}}("x"),
                                inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("1"))
                            )
                        )
                    )
                )
            )
        )

    """
    return Parser.from_string(text).pattern()
