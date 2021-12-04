module TEST-SYNTAX
  imports STRING
  imports INT

syntax Exp [locations]
syntax Exp ::= "" [klabel(foo)]
endmodule

module TEST
  imports TEST-SYNTAX
  imports K-LOCATIONS

syntax Location ::= Loc(Exp, String, Int, Int, Int, Int)
rule #location(E:Exp, File, L1, C1, L2, C2) => Loc(E, File, L1, C1, L2, C2)

endmodule
