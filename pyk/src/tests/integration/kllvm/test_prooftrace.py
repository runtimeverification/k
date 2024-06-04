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

class TestTreeReverse(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module TREE-REVERSE-SYNTAX
            syntax Tree ::= "a" | "b" | "c" | node(Tree, Tree)
            syntax Tree ::= reverse(Tree) [function, total]
            syntax KItem ::= "#Init"
            syntax KItem ::= "#next"
        endmodule

        module TREE-REVERSE
            imports TREE-REVERSE-SYNTAX
            rule [base-case-a] : reverse(a) => a
            rule [base-case-b] : reverse(b) => b
            rule [base-case-c] : reverse(c) => c
            rule [rec-case] :  reverse(node(T1, T2)) => node(reverse(T2), reverse(T1))
            rule [init] : <k> #Init => #next </k>
            rule [next] : <k> #next => reverse(node(a, b)) </k>
        endmodule
        """
        
    KOMPILE_MAIN_MODULE = 'TREE-REVERSE'
    
    HINTS_INPUT_KORE = """
       LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),Lbl'Hash'Init'Unds'TREE-REVERSE-SYNTAX'Unds'KItem{}())))
       """

    def test_parse_proof_hint_reverse_no_ints(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 2 post-initial-configuration events
        assert len(pt.trace) == 9

        # Contents of the k cell in the initial configuration
        kore_pattern = llvm_to_pattern(pt.initial_config.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['name'] == "Lbl'Hash'Init'Unds'TREE-REVERSE-SYNTAX'Unds'KItem"

        # Rule applied in the single (non-functional) rewrite step
        rule_event = pt.trace[0].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 1

        # Second rewrite
        rule_event = pt.trace[1].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        assert hasattr(rule_event, 'rule_ordinal')
        assert hasattr(rule_event, 'substitution')
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 1

        # Function event
        rule_event = pt.trace[2].step_event
        assert isinstance(rule_event, prooftrace.LLVMFunctionEvent)
        assert rule_event.name == "Lblreverse'LParUndsRParUnds'TREE-REVERSE-SYNTAX'Unds'Tree'Unds'Tree{}"
        assert rule_event.relative_position == '0:0:0'
        # Fun events should not have Kore args unless called with a special flag
        assert len(rule_event.args) == 0

        # Simplification rule
        rule_event = pt.trace[3].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 2

        # Function event
        rule_event = pt.trace[4].step_event
        assert isinstance(rule_event, prooftrace.LLVMFunctionEvent)
        assert rule_event.name == "Lblreverse'LParUndsRParUnds'TREE-REVERSE-SYNTAX'Unds'Tree'Unds'Tree{}"
        assert rule_event.relative_position == '0'
        # Fun events should not have Kore args unless called with a special flag
        assert len(rule_event.args) == 0

        # Simplification rule
        rule_event = pt.trace[5].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 1

        # Function event
        rule_event = pt.trace[6].step_event
        assert isinstance(rule_event, prooftrace.LLVMFunctionEvent)
        assert rule_event.name == "Lblreverse'LParUndsRParUnds'TREE-REVERSE-SYNTAX'Unds'Tree'Unds'Tree{}"
        assert rule_event.relative_position == '1'
        # Fun events should not have Kore args unless called with a special flag
        assert len(rule_event.args) == 0

        # Simplification rule
        rule_event = pt.trace[7].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 1

        # Then pattern
        rule_event = pt.trace[8]
        assert rule_event.is_kore_pattern()
        kore_pattern = llvm_to_pattern(rule_event.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert (
            k_cell['args'][0]['args'][0]['name']
            == "Lblnode'LParUndsCommUndsRParUnds'TREE-REVERSE-SYNTAX'Unds'Tree'Unds'Tree'Unds'Tree"
        )
        assert k_cell['args'][0]['args'][0]['args'][0]['name'] == "Lblb'Unds'TREE-REVERSE-SYNTAX'Unds'Tree"
        assert k_cell['args'][0]['args'][0]['args'][1]['name'] == "Lbla'Unds'TREE-REVERSE-SYNTAX'Unds'Tree"

class TestNonRecFunction(ProofTraceTest):
    KOMPILE_DEFINITION = """
    module NON-REC-FUNCTION-SYNTAX
        syntax Foo ::= "a"
                     | bar(Foo)
                     | baz(Foo)
                     | id(Foo) [function, total]
    endmodule

    module NON-REC-FUNCTION
        imports NON-REC-FUNCTION-SYNTAX
        rule [id-rule]: id(X:Foo) => X
        rule [bar-rule]: bar(baz(X:Foo)) => id(id(bar(X)))
    endmodule

        """

    KOMPILE_MAIN_MODULE = 'NON-REC-FUNCTION'

    HINTS_INPUT_KORE = """
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortFoo{}, SortKItem{}}(Lblbar'LParUndsRParUnds'NON-REC-FUNCTION-SYNTAX'Unds'Foo'Unds'Foo{}(Lblbaz'LParUndsRParUnds'NON-REC-FUNCTION-SYNTAX'Unds'Foo'Unds'Foo{}(Lbla'Unds'NON-REC-FUNCTION-SYNTAX'Unds'Foo{}()))))))
        """

    def test_parse_proof_hint_non_rec_function(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 2 post-initial-configuration events
        assert len(pt.trace) == 4

        # Contents of the k cell in the initial configuration
        kore_pattern = llvm_to_pattern(pt.initial_config.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['args'][0]['name'] == "Lblbar'LParUndsRParUnds'NON-REC-FUNCTION-SYNTAX'Unds'Foo'Unds'Foo"

        # Rule applied in the single (non-functional) rewrite step
        rule_event = pt.trace[0].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 3

        # Functional event
        fun_event = pt.trace[1].step_event
        assert isinstance(fun_event, prooftrace.LLVMFunctionEvent)
        assert fun_event.name == "Lblid'LParUndsRParUnds'NON-REC-FUNCTION-SYNTAX'Unds'Foo'Unds'Foo{}"
        assert fun_event.relative_position == '0:0:0'
        assert len(fun_event.args) == 2
        # Check that arguments are a functional event and simplification rule
        assert isinstance(fun_event.args[0].step_event, prooftrace.LLVMFunctionEvent)
        assert fun_event.args[0].step_event.relative_position == '0:0:0:0'
        assert isinstance(fun_event.args[1].step_event, prooftrace.LLVMRuleEvent)

        # Then rule
        rule_event = pt.trace[2].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 1

        # Then pattern
        rule_event = pt.trace[3]
        assert rule_event.is_kore_pattern()
        kore_pattern = llvm_to_pattern(rule_event.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['args'][0]['name'] == "Lblbar'LParUndsRParUnds'NON-REC-FUNCTION-SYNTAX'Unds'Foo'Unds'Foo"

class TestDV(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module DV
            imports DOMAINS
            syntax Foo ::= foo(Int)
                         | succ(Foo)
            rule succ(foo(X:Int)) => foo(X +Int 1)
        endmodule
    """

    KOMPILE_MAIN_MODULE = 'DV'
    KOMPILE_SYNTAX_MODULE = 'DV'

    HINTS_INPUT_KORE = """
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortFoo{}, SortKItem{}}(Lblsucc'LParUndsRParUnds'DV'Unds'Foo'Unds'Foo{}(Lblfoo'LParUndsRParUnds'DV'Unds'Foo'Unds'Int{}(\\dv{SortInt{}}("5")))))))
        """

    def test_parse_proof_hint_dv(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 2 post-initial-configuration events
        assert len(pt.trace) == 3

        # Contents of the k cell in the initial configuration
        kore_pattern = llvm_to_pattern(pt.initial_config.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['args'][0]['name'] == "Lblsucc'LParUndsRParUnds'DV'Unds'Foo'Unds'Foo"
        assert k_cell['args'][0]['args'][0]['args'][0]['name'] == "Lblfoo'LParUndsRParUnds'DV'Unds'Foo'Unds'Int"
        assert k_cell['args'][0]['args'][0]['args'][0]['args'][0]['tag'] == 'DV'
        assert k_cell['args'][0]['args'][0]['args'][0]['args'][0]['value'] == '5'

        # Rule applied in the single (non-functional) rewrite step
        rule_event = pt.trace[0].step_event
        assert isinstance(rule_event, prooftrace.LLVMRuleEvent)
        axiom = repr(definition.get_axiom_by_ordinal(rule_event.rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_event.rule_ordinal)
        assert axiom == axiom_expected
        assert len(rule_event.substitution) == 3

        # Hook event
        hook_event = pt.trace[1].step_event
        assert isinstance(hook_event, prooftrace.LLVMHookEvent)
        assert hook_event.name == 'INT.add'
        assert hook_event.relative_position == '0:0:0:0'
        assert len(hook_event.args) == 3

        fun_event = hook_event.args[0].step_event
        assert isinstance(fun_event, prooftrace.LLVMFunctionEvent)
        assert fun_event.name == "Lbl'UndsPlus'Int'Unds'{}"
        assert fun_event.relative_position == '0:0:0:0'
        assert len(fun_event.args) == 0

        arg1 = hook_event.args[1]
        assert arg1.is_kore_pattern()

        arg2 = hook_event.args[2]
        assert arg2.is_kore_pattern()

        # Then pattern
        rule_event = pt.trace[2]
        assert rule_event.is_kore_pattern()
        kore_pattern = llvm_to_pattern(rule_event.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert k_cell['args'][0]['args'][0]['name'] == "Lblfoo'LParUndsRParUnds'DV'Unds'Foo'Unds'Int"
        assert k_cell['args'][0]['args'][0]['args'][0]['tag'] == 'DV'
        assert k_cell['args'][0]['args'][0]['args'][0]['value'] == '6'


class TestConcurrentCounters(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module CONCURRENT-COUNTERS-SYNTAX
            imports INT-SYNTAX
            syntax State ::= state(Int, Int)
        endmodule

        module CONCURRENT-COUNTERS
            imports INT
            imports CONCURRENT-COUNTERS-SYNTAX
            rule [count-rule1] : state(M, N) => state((M -Int 1), (N +Int M))
                requires M >=Int 3 [priority(50)]
            rule [count-rule2] : state(M, N) => state((M -Int 1), (N -Int 1))
                requires M >=Int 1 [priority(60)]
        endmodule
    """

    KOMPILE_MAIN_MODULE = 'CONCURRENT-COUNTERS'

    HINTS_INPUT_KORE = """    
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortState{}, SortKItem{}}(Lblstate'LParUndsCommUndsRParUnds'CONCURRENT-COUNTERS-SYNTAX'Unds'State'Unds'Int'Unds'Int{}(\\dv{SortInt{}}("4"),\\dv{SortInt{}}("0"))))))
    """

    def test_parse_concurrent_counters(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        # main purpose of the test is to check the sequence of events in the trace with
        # successful and failed side condition checks
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 2 post-initial-configuration events
        assert len(pt.trace) == 37

        # Check types
        expected_events = {
            prooftrace.LLVMRuleEvent: [3, 9, 18, 27],
            prooftrace.LLVMSideConditionEventEnter: [0, 6, 12, 15, 21, 24, 30, 33],
            prooftrace.LLVMSideConditionEventExit: [1, 2, 8, 14, 17, 23, 26, 32, 35],
            prooftrace.LLVMHookEvent: [1, 4, 5, 7, 10, 11, 13, 16, 19, 20, 22, 25, 28, 29, 31, 34],
        }
        for step, event in enumerate(pt.trace):
            if event.is_kore_pattern():
                continue
            elif isinstance(event.step_event, prooftrace.LLVMRuleEvent):
                assert step in expected_events[prooftrace.LLVMRuleEvent], f'We expect {str(step)} to be of type {type(event).__name__}'
            elif isinstance(event.step_event, prooftrace.LLVMSideConditionEventEnter):
                assert (
                    step in expected_events[prooftrace.LLVMSideConditionEventEnter]
                ), f'We expect {str(step)} to be of type {type(event).__name__}'
            elif isinstance(event.step_event, prooftrace.LLVMSideConditionEventExit):
                assert (
                    step in expected_events[prooftrace.LLVMSideConditionEventExit]
                ), f'We expect {str(step)} to be of type {type(event).__name__}'
            elif isinstance(event.step_event, prooftrace.LLVMHookEvent):
                assert step in expected_events[prooftrace.LLVMHookEvent], f'We expect {str(step)} to be of type {type(event).__name__}'
            else:
                raise NotImplementedError()

        # Check axiom ordinals
        assert isinstance(pt.trace[0].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[0].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)
        assert axiom == axiom_expected

        assert isinstance(pt.trace[2].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[2].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[3].step_event, prooftrace.LLVMRuleEvent)
        rule_ordinal = pt.trace[3].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[6].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[6].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[8].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[8].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[9].step_event, prooftrace.LLVMRuleEvent)
        rule_ordinal = pt.trace[9].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[12].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[12].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[14].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[14].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[15].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[15].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[17].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[17].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[18].step_event, prooftrace.LLVMRuleEvent)
        rule_ordinal = pt.trace[18].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[21].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[21].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[23].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[23].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[24].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[24].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[26].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[26].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[27].step_event, prooftrace.LLVMRuleEvent)
        rule_ordinal = pt.trace[27].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[30].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[30].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[32].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[32].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[33].step_event, prooftrace.LLVMSideConditionEventEnter)
        rule_ordinal = pt.trace[33].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)

        assert isinstance(pt.trace[35].step_event, prooftrace.LLVMSideConditionEventExit)
        rule_ordinal = pt.trace[35].step_event.rule_ordinal
        axiom = repr(definition.get_axiom_by_ordinal(rule_ordinal))
        axiom_expected = get_pattern_from_ordinal(definition_text, rule_ordinal)



class TestPeano(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module PEANO-SYNTAX
            syntax Nat ::= "0"
                        | s(Nat)        [overload(Nat)]
            syntax Exp ::= Nat
            syntax Exp ::= s(Exp)        [overload(Nat), strict]
            syntax Exp ::= add(Exp, Exp) [seqstrict]
            syntax Exp ::= mul(Exp, Exp) [seqstrict]
        endmodule

        module PEANO
            imports PEANO-SYNTAX
            syntax KResult ::= Nat
            rule [add-0] : add(0, M:Nat) => M
            rule [add-1] : add(s(N:Nat), M:Nat) => s(add(N, M))
            rule [mul-0] : mul(0, _:Nat) => 0
            rule [mul-1] : mul(s(N:Nat), M:Nat) => add(M, mul(N, M))
        endmodule
    """

    KOMPILE_MAIN_MODULE = 'PEANO'

    HINTS_INPUT_KORE = """    
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortExp{}, SortKItem{}}(Lblmul'LParUndsCommUndsRParUnds'PEANO-SYNTAX'Unds'Exp'Unds'Exp'Unds'Exp{}(inj{SortNat{}, SortExp{}}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbl0'Unds'PEANO-SYNTAX'Unds'Nat{}())))),inj{SortNat{}, SortExp{}}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbls'LParUndsRParUnds'PEANO-SYNTAX'Unds'Nat'Unds'Nat{}(Lbl0'Unds'PEANO-SYNTAX'Unds'Nat{}())))))))))))

    """
    def test_parse_proof_hint_peano(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 461 post-initial-configuration events
        assert len(pt.trace) == 404

class TestIMP5(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module IMP5-SYNTAX
            imports INT-SYNTAX
            imports BOOL-SYNTAX
            syntax Id2 ::= "x1" | "x2" | "x3" | "x4" | "x5" | "ret"
            syntax AExp  ::= Int | Id2
                            | "-" Int                    [format(%1%2)]
                            | AExp "/" AExp              [left, seqstrict, color(pink)]
                            | "(" AExp ")"               [bracket]
                            | AExp "*" AExp              [left, seqstrict]
                            | AExp "%" AExp              [left, seqstrict]
                            > AExp "+" AExp              [left, seqstrict, color(pink)]
                            | AExp "-" AExp              [left, seqstrict, color(pink)]
            syntax BExp  ::= Bool
                            | AExp "==" AExp             [seqstrict]
                            | AExp "<=" AExp             [seqstrict]
                            | AExp "<" AExp              [seqstrict]
                            | AExp ">=" AExp             [seqstrict]
                            | AExp ">" AExp              [seqstrict]
                            | "!" BExp                   [strict, color(pink)]
                            | "(" BExp ")"               [bracket]
                            // | "nondet"
                            > BExp "&&" BExp             [left, strict(1), color(pink)]
            syntax Block ::= "{" "}"
                            | "{" Stmt "}"               [format(%1%i%n%2%d%n%3)]
            syntax Stmt  ::= Block
                            | Id2 "=" AExp ";"            [strict(2), color(pink), format(%1 %2 %3%4)]
                            | "if" "(" BExp ")"
                            Block "else" Block         [strict(1), colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7)]
                            | "while" "(" BExp ")" Block [colors(yellow,white,white), format(%1 %2%3%4 %5)]
                            > Stmt Stmt                  [left, format(%1%n%2)]
            syntax Pgm ::= Stmt
            syntax Pgm ::= "int" Ids ";" Stmt           [format(%1 %2%3%n%4), colors(yellow,pink)]
            syntax Ids ::= List{Id2,","}                 [format(%1%2 %3)]
            syntax Vars5 ::= Int "," Int "," Int "," Int "," Int "," Int
        endmodule

        module IMP5
            imports IMP5-SYNTAX
            imports INT
            imports BOOL
            syntax KResult ::= Int | Bool
            configuration <T color="yellow">
                            <k color="green"> $PGM:Pgm </k>
                            <s color="red"> ( 0 , 0 , 0 , 0 , 0 , 0 ):Vars5 </s>
                            </T>
            rule <k> x1 => I ...</k> <s> I , _ , _ , _ , _ , _ </s>
            rule <k> x2 => I ...</k> <s> _ , I , _ , _ , _ , _ </s>
            rule <k> x3 => I ...</k> <s> _ , _ , I , _ , _ , _ </s>
            rule <k> x4 => I ...</k> <s> _ , _ , _ , I , _ , _ </s>
            rule <k> x5 => I ...</k> <s> _ , _ , _ , _ , I , _ </s>
            rule <k> ret => I ...</k> <s> _ , _ , _ , _ , _ , I </s>
            rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
            rule I1 * I2 => I1 *Int I2
            rule I1 % I2 => I1 %Int I2
            rule I1 + I2 => I1 +Int I2
            rule I1 - I2 => I1 -Int I2
            rule - I1 => 0 -Int I1
            rule I1 == I2 => I1 ==Int I2
            rule I1 <= I2 => I1 <=Int I2
            rule I1 < I2 => I1 <Int I2
            rule I1 >= I2 => I1 >=Int I2
            rule I1 > I2 => I1 >Int I2
            rule ! T => notBool T
            // We do not have C to avoid requires
            rule true && B => B // requires C
            rule false && _ => false // requires notBool C
            rule {} => .K
            rule {S} => S
            rule <k> x1 = I:Int; => .K ...</k> <s> ( _ => I ) , _ , _ , _ , _ , _ </s>
            rule <k> x2 = I:Int; => .K ...</k> <s> _ , ( _ => I ) , _ , _ , _ , _ </s>
            rule <k> x3 = I:Int; => .K ...</k> <s> _ , _ , ( _ => I ) , _ , _ , _ </s>
            rule <k> x4 = I:Int; => .K ...</k> <s> _ , _ , _ , ( _ => I ) , _  , _ </s>
            rule <k> x5 = I:Int; => .K ...</k> <s> _ , _ , _ , _ , ( _ => I ) , _ </s>
            rule <k> ret = I:Int; => .K ...</k> <s> _ , _ , _ , _ , _ , ( _ => I ) </s>
            rule S1:Stmt S2:Stmt => S1 ~> S2
            rule if (true)  S else _ => S // requires C
            rule if (false) _ else S => S // requires notBool C
            rule while (B) S => if (B) {S while (B) S} else {}
            // We do not support these void declarations
            // rule <k> int (X,Xs => Xs);_ </k> <state> _:Map (.Map => X|->0) </state>
            // We have _L here instead of .Ids because we are not doing anything with declaration
            rule int _L; S => S
        endmodule
    """

    KOMPILE_MAIN_MODULE = 'IMP5'

    HINTS_INPUT_KORE = """    
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortPgm{}, SortKItem{}}(inj{SortBlock{}, SortPgm{}}(Lbl'LBraRBraUnds'IMP5-SYNTAX'Unds'Block{}())))))
    """
    def test_parse_proof_hint_imp5(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None

        definition.preprocess()
        definition_text = repr(definition).split('\n')

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 15 initialization events
        assert len(pt.pre_trace) == 15

        # 2 post-initial-configuration events
        assert len(pt.trace) == 2

class TestBuiltInHookEvents(ProofTraceTest):
    KOMPILE_DEFINITION = """
        module BUILTIN-HOOK-EVENTS-SYNTAX
            imports BOOL-SYNTAX
            syntax Foo ::= foo(Bool)
        endmodule

        module BUILTIN-HOOK-EVENTS
            imports BOOL
            imports BUILTIN-HOOK-EVENTS-SYNTAX
            rule foo(B) => notBool notBool B
        endmodule
    """

    KOMPILE_MAIN_MODULE = 'BUILTIN-HOOK-EVENTS'

    HINTS_INPUT_KORE = """    
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortFoo{}, SortKItem{}}(Lblfoo'LParUndsRParUnds'BUILTIN-HOOK-EVENTS-SYNTAX'Unds'Foo'Unds'Bool{}(\\dv{SortBool{}}("true"))))))
    """
    def test_parse_proof_hint_builtin_hook_events(self, hints: bytes, header: prooftrace.kore_header, definition_file: str) -> None:
        definition = parse_definition(definition_file)
        assert definition is not None
        
        definition.preprocess()
        definition_text = repr(definition).split('\n')
        
        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None
        
        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 2 post-initial-configuration events
        assert len(pt.trace) == 3

        # Contents of the k cell in the initial configuration
        kore_pattern = llvm_to_pattern(pt.initial_config.kore_pattern)
        k_cell = kore_pattern.patterns[0].dict['args'][0]
        assert k_cell['name'] == 'kseq'
        assert (
            k_cell['args'][0]['args'][0]['name'] == "Lblfoo'LParUndsRParUnds'BUILTIN-HOOK-EVENTS-SYNTAX'Unds'Foo'Unds'Bool"
        )
        assert k_cell['args'][1]['name'] == 'dotk'

        # Rewrite rule
        assert isinstance(pt.trace[0].step_event, prooftrace.LLVMRuleEvent)
        rule_ordinal = pt.trace[0].step_event.rule_ordinal
        repr(definition.get_axiom_by_ordinal(rule_ordinal))
        get_pattern_from_ordinal(definition_text, rule_ordinal)

        # Hook event with a nested event
        assert isinstance(pt.trace[1].step_event, prooftrace.LLVMHookEvent)
        assert pt.trace[1].step_event.name == 'BOOL.not'
        assert pt.trace[1].step_event.relative_position == '0:0:0'
        assert len(pt.trace[1].step_event.args) == 2
        arg1 = pt.trace[1].step_event.args[0].step_event
        arg2 = pt.trace[1].step_event.args[1]
        assert isinstance(arg1, prooftrace.LLVMHookEvent)
        assert arg1.name == 'BOOL.not'
        assert arg1.relative_position == '0:0:0:0'
        assert len(arg1.args) == 1
        assert arg1.args[0].is_kore_pattern()
        assert arg2.is_kore_pattern()

        # Final configuration
        assert pt.trace[2].is_kore_pattern()
