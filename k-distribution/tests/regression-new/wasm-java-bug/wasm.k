module WASM
    imports KSEQ

    configuration
      <k> $PGM:Instrs </k>

    syntax PlainInstr ::= "foo" | "bar"

    syntax Instr ::= PlainInstr
                   | "(" PlainInstr Instrs ")" [prefer]
 // ------------------------------------------

    syntax Instrs ::= List{Instr, ""}
 // ---------------------------------
endmodule
