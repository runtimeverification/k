from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.prelude.ml import mlTop
from pyk.testing import CTermSymbolicTest, KPrintTest

if TYPE_CHECKING:
    from collections.abc import Iterable

    from pyk.cterm import CTermSymbolic
    from pyk.ktool.kprint import KPrint


EXECUTE_TEST_DATA: Iterable[tuple[str]] = (('branch',),)


class TestMultipleDefinitionsProof(CTermSymbolicTest, KPrintTest):
    KOMPILE_DEFINITION = """
        module MULTIPLE-DEFINITIONS
          imports A
          imports B
          imports BOOL

          syntax KItem  ::= a(KItem) [symbol(a)]
                          | "b"
                          | "c"
          rule a(X) => b requires isInt(X)
          rule a(X) => b requires notBool isInt(X)
          rule b => c
        endmodule

        module A
          syntax Int
        endmodule

        module B
          syntax Int
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'MULTIPLE-DEFINITIONS'
    KOMPILE_ARGS = {'syntax_module': 'MULTIPLE-DEFINITIONS'}
    LLVM_ARGS = {'syntax_module': 'MULTIPLE-DEFINITIONS'}

    @staticmethod
    def config() -> CTerm:
        return CTerm(
            KApply(
                '<generatedTop>',
                KApply('<k>', KSequence(KApply('a', [KVariable('X')]))),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
            (mlTop(),),
        )

    @pytest.mark.parametrize(
        'test_id',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kprint: KPrint,
        cterm_symbolic: CTermSymbolic,
        test_id: str,
    ) -> None:
        exec_res = cterm_symbolic.execute(self.config(), depth=1)
        split_next_terms = exec_res.next_states
        split_k = kprint.pretty_print(exec_res.state.cell('K_CELL'))
        split_next_k = [kprint.pretty_print(exec_res.state.cell('K_CELL')) for _ in split_next_terms]

        assert exec_res.depth == 0
        assert len(split_next_terms) == 2
        assert 'a ( X:KItem ) ~> .K' == split_k
        assert [
            'a ( X:KItem ) ~> .K',
            'a ( X:KItem ) ~> .K',
        ] == split_next_k

        step_1_res = cterm_symbolic.execute(split_next_terms[0][0], depth=1)
        step_1_k = kprint.pretty_print(step_1_res.state.cell('K_CELL'))
        assert 'c ~> .K' == step_1_k

        step_2_res = cterm_symbolic.execute(split_next_terms[1][0], depth=1)
        step_2_k = kprint.pretty_print(step_2_res.state.cell('K_CELL'))
        assert 'c ~> .K' == step_2_k
