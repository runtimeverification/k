from __future__ import annotations

import pyk.kllvm.hints.prooftrace as prooftrace
from pyk.kllvm.convert import llvm_to_pattern
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


def get_pattern_from_ordinal(definition_text: list[str], ordinal: int) -> str:
    axiom_ordinal = 'ordinal{}("' + str(ordinal) + '")'
    line = next((i + 1 for i, l in enumerate(definition_text) if axiom_ordinal in l), None)
    assert line is not None
    return definition_text[line - 1].strip()

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

    def test_proof_trace(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

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
        axiom_expected = get_pattern_from_ordinal(definition_text, axiom_ordinal)
        assert axiom == axiom_expected

        # check that the second event is the rewrite b() => c()
        assert pt.trace[1].is_step_event()
        assert isinstance(pt.trace[1].step_event, prooftrace.LLVMRewriteEvent)
        axiom_ordinal = pt.trace[1].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(axiom_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, axiom_ordinal)
        assert axiom == axiom_expected

        # check that the third event is a configuration
        assert pt.trace[2].is_kore_pattern()

class TestSingleRewrite(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module SINGLE-REWRITE-SYNTAX
            syntax Foo ::= FooA() | FooB()
        endmodule

        module SINGLE-REWRITE
            imports SINGLE-REWRITE-SYNTAX
            rule [a-to-b]: FooA() => FooB()
        endmodule
        """
        
    KOMPILE_MAIN_MODULE = 'SINGLE-REWRITE'
    
    HINTS_INPUT_KORE = """LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortFoo{}, SortKItem{}}(LblFooA'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo{}()))))"""


    def test_parse_proof_hint_single_rewrite(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization event
        assert len(pt.pre_trace) == 11

        # 2 post-initial-configuration events
        assert len(pt.trace) == 2

        # Contents of the k cell in the initial configuration
        kore_pattern = llvm_to_pattern(pt.initial_config.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['args'][0]['name'] == "LblFooA'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
        assert k_cell['args'][1]['name'] == 'dotk'

        # Rule applied in the single (non-functional) rewrite step
        rule_event = pt.trace[0].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)

        assert hasattr(rule_event, 'rule_ordinal')
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected

        # Contents of the k cell in the final configuration
        final_config = pt.trace[1]
        assert final_config.is_kore_pattern()
        kore_pattern = llvm_to_pattern(final_config.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['args'][0]['name'] == "LblFooB'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
        assert k_cell['args'][1]['name'] == 'dotk'
