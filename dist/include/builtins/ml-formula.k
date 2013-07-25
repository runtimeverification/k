require "simplification.k"

module ML-FORMULA-SYNTAX
  syntax MLFormula ::= Bag "/\\ML" Bool
endmodule

module ML-FORMULA
  imports ML-FORMULA-SYNTAX
  imports SIMPLIFICATION
endmodule