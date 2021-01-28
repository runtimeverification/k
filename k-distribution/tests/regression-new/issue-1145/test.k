module TEST-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX

  syntax AList ::= List{String, ";"}
endmodule

module TEST
  imports TEST-SYNTAX

  rule _I:Int => .AList
  configuration <k> $PGM:Int </k>
endmodule
