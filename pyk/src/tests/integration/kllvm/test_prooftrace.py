from __future__ import annotations

import pyk.kllvm.hints.prooftrace as prooftrace
from pyk.kllvm.parser import parse_definition
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
    
    def get_pattern_from_ordinal(self, definition_text, ordinal):
        axiom_ordinal = 'ordinal{}("' + str(ordinal) + '")'
        line = next((i+1 for i, l in enumerate(definition_text) if axiom_ordinal in l), None)
        return definition_text[line-1].strip()

    def test_proof_trace(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None
        
        definition.preprocess()
        definition_text = repr(definition).split("\n")
        
        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # check that there is a initial configuration
        assert pt.initial_config.is_kore_pattern()

        # check that the trace after the initial configuration is 3 events long
        assert len(pt.trace) == 3

        # check that the first event is the rewrite a() => b()
        assert pt.trace[0].is_step_event()
        assert isinstance(pt.trace[0].step_event, prooftrace.LLVMRewriteEvent)
        axiom_ordinal = pt.trace[0].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(axiom_ordinal))
        axiom_expected = self.get_pattern_from_ordinal(definition_text, axiom_ordinal)
        assert axiom == axiom_expected

        # check that the second event is the rewrite b() => c()
        assert pt.trace[1].is_step_event()
        assert isinstance(pt.trace[1].step_event, prooftrace.LLVMRewriteEvent)
        axiom_ordinal = pt.trace[1].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(axiom_ordinal))
        axiom_expected = self.get_pattern_from_ordinal(definition_text, axiom_ordinal)
        assert axiom == axiom_expected

        # check that the third event is a configuration
        assert pt.trace[2].is_kore_pattern()
