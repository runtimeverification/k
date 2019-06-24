module TEST-COMMON
  imports INT-SYNTAX
  imports BOOL

  syntax ShiftInst ::= Int "=" "shift" Int "," Int [hybrid, seqstrict(2,3)]

endmodule

module TEST
    imports TEST-COMMON
    imports DEFAULT-STRATEGY

    syntax KResult ::= Int

    configuration <k> $PGM:K </k> <s/>
endmodule
