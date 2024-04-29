from __future__ import annotations

from typing import cast

import pyk.kllvm.load  # noqa: F401
import pyk.kllvm.prooftrace as prooftrace
from pyk.testing import ProofTraceTest


class TestProofTrace(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module TEST-PROOF-TRACE-SYNTAX
          syntax Foo ::= a() | b() | c()
        endmodule
        
        module TEST-PROOF-TRACE
          imports TEST-PROOF-TRACE-SYNTAX
          rule a() => b()
          rule b() => c()
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'TEST-PROOF-TRACE'
    HINTS_INPUT_KORE = r"""
        LblinitGeneratedTopCell{}(
          Lbl'Unds'Map'Unds'{}(
            Lbl'Stop'Map{}(),
            Lbl'UndsPipe'-'-GT-Unds'{}(
               inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$PGM")),
               inj{SortFoo{}, SortKItem{}}(Lbla'LParRParUnds'TEST-PROOF-TRACE-SYNTAX'Unds'Foo{}())
            )
          )
        )
    """

    def test_proof_trace(self, hints: bytes) -> None:
        pt = prooftrace.LLVMRewriteTrace.parse(hints)
        assert pt is not None

        # check that there is a initial configuration
        assert pt.initial_config.is_kore_pattern()

        # check that the trace after the initial configuration is 3 events long
        assert len(pt.trace) == 3

        # check that the first event is the rewrite a() => b()
        assert pt.trace[0].is_step_event()
        rewrite_event = cast('prooftrace.LLVMRewriteEvent', pt.trace[0].step_event)
        assert rewrite_event.rule_ordinal == 96

        # check that the second event is the rewrite b() => c()
        assert pt.trace[1].is_step_event()
        rewrite_event = cast('prooftrace.LLVMRewriteEvent', pt.trace[1].step_event)
        assert rewrite_event.rule_ordinal == 97

        # check that the third event is a configuration
        assert pt.trace[2].is_kore_pattern()
