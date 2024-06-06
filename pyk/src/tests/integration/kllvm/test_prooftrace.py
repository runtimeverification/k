from __future__ import annotations

from typing import TYPE_CHECKING

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

if TYPE_CHECKING:
    from pathlib import Path


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

    def get_pattern_from_ordinal(self, definition_text: list[str], ordinal: int) -> str:
        axiom_ordinal = 'ordinal{}("' + str(ordinal) + '")'
        line = next((i + 1 for i, l in enumerate(definition_text) if axiom_ordinal in l), None)
        assert line is not None
        return definition_text[line - 1].strip()

    def test_proof_trace(self, hints: bytes, header: prooftrace.KoreHeader, definition_file: str) -> None:
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

    def test_streaming_parser_iter(self, header: prooftrace.KoreHeader, hints_file: Path) -> None:
        # read the hints file and get the iterator for the proof trace
        it = prooftrace.LLVMRewriteTraceIterator.from_file(hints_file, header)
        assert it.version == 11

        # Test that the __iter__ is working
        list_of_events = list(it)

        # Test length of the list
        assert len(list_of_events) == 13

        # Test the type of the events
        for event in list_of_events:
            if event.type.is_pre_trace:
                continue
            elif event.type.is_initial_config:
                assert event.event.is_kore_pattern()
            elif event.type.is_trace:
                if event.event.is_step_event():
                    assert isinstance(event.event.step_event, prooftrace.LLVMRewriteEvent)
                else:
                    assert event.event.is_kore_pattern()

    def test_streaming_parser_next(self, header: prooftrace.KoreHeader, hints_file: Path, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        # read the hints file and get the iterator for the proof trace
        it = prooftrace.LLVMRewriteTraceIterator.from_file(hints_file, header)
        assert it.version == 11

        # skip pre-trace events
        while True:
            event0 = next(it)
            if event0 is None or not event0.type.is_pre_trace:
                break

        # check that the first event is the initial configuration
        assert event0.type.is_initial_config
        assert event0.event.is_kore_pattern()

        # check that the first event is the rewrite a() => b()
        event1 = next(it)
        assert event1.event.is_step_event()
        assert isinstance(event1.event.step_event, prooftrace.LLVMRewriteEvent)
        axiom_ordinal = event1.event.step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(axiom_ordinal))
        axiom_expected = self.get_pattern_from_ordinal(definition_text, axiom_ordinal)
        assert axiom == axiom_expected

        # check that the second event is the rewrite b() => c()
        event2 = next(it)
        assert event2.event.is_step_event()
        assert isinstance(event2.event.step_event, prooftrace.LLVMRewriteEvent)
        axiom_ordinal = event2.event.step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(axiom_ordinal))
        axiom_expected = self.get_pattern_from_ordinal(definition_text, axiom_ordinal)
        assert axiom == axiom_expected

        event3 = next(it)
        assert event3.type.is_trace
        assert event3.event.is_kore_pattern()
