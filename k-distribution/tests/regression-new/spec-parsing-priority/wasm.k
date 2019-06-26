module WASM
    imports KSEQ

    configuration
      <k> $PGM:Instrs </k>

    syntax PlainInstr ::= "foo" | "bar"
 // -----------------------------------

    syntax Instr ::= PlainInstr
                   | "(" PlainInstr Instrs ")" [prefer]
 // ---------------------------------------------------
    rule <k> ( foo ) ( bar ) => . ... </k>

    syntax Instrs ::= List{Instr, ""}
 // ---------------------------------
endmodule
