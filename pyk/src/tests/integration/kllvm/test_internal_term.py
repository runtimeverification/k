from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.testing import RuntimeTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kllvm.ast import Pattern
    from pyk.kllvm.runtime import Runtime


@pytest.mark.skip(
    reason="This test doesn't conform with the current version of LLVM GC. It should be updated or deleted soon."
)
class TestInternalTerm(RuntimeTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    def test_str_llvm_backend_issue_724(self, runtime: Runtime, start_pattern: Pattern) -> None:
        for _ in range(10000):
            term = runtime._module.InternalTerm(start_pattern)
            term.step(-1)
            # just checking that str doesn't crash
            str(term)


@pytest.fixture
def start_pattern(load_kllvm: None) -> Pattern:
    from pyk.kllvm.parser import Parser

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
