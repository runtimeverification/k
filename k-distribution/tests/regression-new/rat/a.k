requires "rat.md"

module A

imports RAT

configuration <T>
  <k> $PGM:Pgm </k>
</T>

syntax Cmd ::= Rat ";"
             | Bool ";"
syntax Pgm ::= List{Cmd,""}

syntax Rat ::= "(" Rat ")" [bracket]

endmodule
