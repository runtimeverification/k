requires "rat.k"

module A

imports RAT
imports RAT-NON-KORE

configuration <T>
  <k> $PGM:Pgm </k>
</T>

syntax Cmd ::= Rat ";"
             | Bool ";"
syntax Pgm ::= List{Cmd,""}


syntax Rat ::= "<" Int "," Int ">"

// to distinghish constructor terms from unevaluated function terms
rule < A , B >Rat ; => < A , B > ; [anywhere]

endmodule
