module WASM
    imports KSEQ

    configuration
      <k> $PGM:Instrs </k>

    syntax PlainInstr ::= "foo" | "bar"
 // -----------------------------------
    rule <k> foo => . ... </k>
    rule <k> bar => . ... </k>

    syntax Instr ::= PlainInstr
                   | "(" PlainInstr Instrs ")" [prefer]
 // ---------------------------------------------------
    rule <k> ( PI:PlainInstr IS:Instrs ):Instr => IS ~> PI ... </k>

    syntax Instrs ::= List{Instr, ""}
 // ---------------------------------
    rule <k> I:Instr IS:Instrs => I ~> IS ... </k>
endmodule
