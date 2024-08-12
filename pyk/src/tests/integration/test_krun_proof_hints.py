from __future__ import annotations

from typing import TYPE_CHECKING

import pyk.kllvm.hints.prooftrace as prooftrace
from pyk.kore.parser import KoreParser
from pyk.testing import KRunTest

if TYPE_CHECKING:
    from pyk.ktool.krun import KRun


class Test0Decrement(KRunTest):
    KOMPILE_DEFINITION = """
        module DECREMENT-SYNTAX
            syntax Nat ::= "0" | s(Nat)
        endmodule

        module DECREMENT
            imports DECREMENT-SYNTAX
            rule [decrement] : s(N:Nat) => N
        endmodule
    """

    KOMPILE_MAIN_MODULE = 'DECREMENT'
    KOMPILE_BACKEND = 'llvm'
    KOMPILE_ARGS = {'llvm_proof_hint_instrumentation': True}

    HINTS_INPUT_KORE = """
        LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\\dv{SortKConfigVar{}}("$PGM")),inj{SortNat{}, SortKItem{}}(Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}()))))
    """

    HINTS_OUTPUT = """version: 11
hook: MAP.element Lbl'UndsPipe'-'-GT-Unds'{} ()
  function: Lbl'UndsPipe'-'-GT-Unds'{} ()
  arg: kore[\\dv{SortKConfigVar{}}("$PGM")]
  arg: kore[Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}()]
hook result: kore[Lbl'UndsPipe'-'-GT-Unds'{}(\\dv{SortKConfigVar{}}("$PGM"),Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}())]
hook: MAP.unit Lbl'Stop'Map{} ()
  function: Lbl'Stop'Map{} ()
hook result: kore[Lbl'Stop'Map{}()]
hook: MAP.concat Lbl'Unds'Map'Unds'{} ()
  function: Lbl'Unds'Map'Unds'{} ()
  arg: kore[Lbl'Stop'Map{}()]
  arg: kore[Lbl'UndsPipe'-'-GT-Unds'{}(\\dv{SortKConfigVar{}}("$PGM"),Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}())]
hook result: kore[Lbl'UndsPipe'-'-GT-Unds'{}(\\dv{SortKConfigVar{}}("$PGM"),Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}())]
function: LblinitGeneratedTopCell{} ()
rule: 99 1
  VarInit = kore[Lbl'UndsPipe'-'-GT-Unds'{}(\\dv{SortKConfigVar{}}("$PGM"),Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}())]
function: LblinitKCell{} (0)
rule: 100 1
  VarInit = kore[Lbl'UndsPipe'-'-GT-Unds'{}(\\dv{SortKConfigVar{}}("$PGM"),Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}())]
function: Lblproject'Coln'KItem{} (0:0)
  hook: MAP.lookup LblMap'Coln'lookup{} (0:0:0:0)
    function: LblMap'Coln'lookup{} (0:0:0:0)
    arg: kore[Lbl'UndsPipe'-'-GT-Unds'{}(\\dv{SortKConfigVar{}}("$PGM"),Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}())]
    arg: kore[\\dv{SortKConfigVar{}}("$PGM")]
  hook result: kore[Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}()]
rule: 139 1
  VarK = kore[Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}()]
function: LblinitGeneratedCounterCell{} (1)
rule: 98 0
config: kore[Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}(),dotk{}())),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}("0")))]
config: kore[Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbl0'Unds'DECREMENT-SYNTAX'Unds'Nat{}(),dotk{}())),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}("0")))]
"""

    def test_parse_proof_hint_0_decrement(self, krun: KRun, header: prooftrace.KoreHeader) -> None:
        pgm = KoreParser(self.HINTS_INPUT_KORE).pattern()

        hints = krun.run_proof_hint(
            pgm,
            parser='cat',
            term=True,
            proof_hint=True,
        )

        pt = prooftrace.LLVMRewriteTrace.parse(hints, header)
        assert pt is not None

        # 11 initialization events
        assert len(pt.pre_trace) == 11

        # 1 post-initial-configuration event
        assert len(pt.trace) == 1

        # Check if the proof trace is correct
        assert str(pt) == self.HINTS_OUTPUT
