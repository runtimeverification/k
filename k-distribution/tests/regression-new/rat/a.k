requires "rat.k"

module A

imports RAT

configuration <T>
  <k> $PGM:Pgm </k>
</T>

syntax Cmd ::= Rat ";"
             | Bool ";"
syntax Pgm ::= List{Cmd,""}

syntax Rat ::= "(" Rat ")" [bracket]

syntax Rat ::= "<" Int "," Int ">"

// to distinghish constructor terms from unevaluated function terms
rule < A , B >Rat ; => < A , B > ; [anywhere]

endmodule
