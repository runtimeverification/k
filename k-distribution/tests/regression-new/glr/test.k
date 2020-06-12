module TEST-SYNTAX

  syntax A ::= B | C
  syntax B ::= D
  syntax C ::= D
  syntax D ::= "foo"

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:A </k>

endmodule
