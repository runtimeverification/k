from __future__ import annotations

import pyk.kllvm.hints.prooftrace as prooftrace
import pyk.kllvm.load  # noqa: F401
from pyk.kore.prelude import (
    SORT_K_CONFIG_VAR,
    SORT_K_ITEM,
    SortApp,
    init_generated_top_cell,
    inj,
    k_config_var,
    map_pattern,
)
from pyk.kore.syntax import App
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

    program_pattern = App("Lbla\'LParRParUnds\'TEST-PROOF-TRACE-SYNTAX\'Unds\'Foo")

    HINTS_INPUT_KORE = init_generated_top_cell(
        map_pattern(
            (
                inj(SORT_K_CONFIG_VAR, SORT_K_ITEM, k_config_var('$PGM')),
                inj(SortApp('SortFoo'), SORT_K_ITEM, program_pattern),
            )
        )
    ).text

    def test_proof_trace(self, hints: bytes) -> None:
        pt = prooftrace.LLVMRewriteTrace.parse(hints)
        assert pt is not None

        # check that there is a initial configuration
        assert pt.initial_config.is_kore_pattern()

        # check that the trace after the initial configuration is 3 events long
        assert len(pt.trace) == 3

        # check that the first event is the rewrite a() => b()
        assert pt.trace[0].is_step_event()
        assert isinstance(pt.trace[0].step_event, prooftrace.LLVMRewriteEvent)
        assert pt.trace[0].step_event.rule_ordinal == 97

        # check that the second event is the rewrite b() => c()
        assert pt.trace[1].is_step_event()
        assert isinstance(pt.trace[1].step_event, prooftrace.LLVMRewriteEvent)
        assert pt.trace[1].step_event.rule_ordinal == 98

        # check that the third event is a configuration
        assert pt.trace[2].is_kore_pattern()
