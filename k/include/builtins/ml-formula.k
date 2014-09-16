// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "simplification.k"

module ML-FORMULA-SYNTAX
  syntax MLFormula ::= Bag "/\\ML" Bool
endmodule

module ML-FORMULA
  imports ML-FORMULA-SYNTAX
  imports SIMPLIFICATION
endmodule