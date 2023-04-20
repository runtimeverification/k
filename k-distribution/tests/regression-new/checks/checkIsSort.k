module CHECKISSORT-SYNTAX
  imports BOOL-SYNTAX
  imports BASIC-K

  syntax Bool ::= isNonAddr(KItem) [function]
  syntax NonAddr ::= nonAddr(KItem)
endmodule

module CHECKISSORT
  imports CHECKISSORT-SYNTAX
endmodule
