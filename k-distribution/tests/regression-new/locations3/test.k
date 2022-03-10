module TEST-SYNTAX
  imports STRING
  imports INT

syntax Exps [locations]
syntax Exps ::= NeList{Exp,","}
syntax Exp ::= "foo"
endmodule

module TEST
  imports TEST-SYNTAX
  imports K-LOCATIONS

configuration <k> $PGM:Exps </k>

syntax Location ::= Loc(Exps, String, Int, Int, Int, Int)
rule #location(E:Exps, File, L1, C1, L2, C2) => Loc(E, File, L1, C1, L2, C2)

endmodule
