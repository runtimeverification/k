// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "bool.k"
require "int.k"
module FOL
  imports BOOL-HOOKS
  imports INT-HOOKS

  syntax Fol ::= Bool
               | "notFol" Fol [function]
               > left:
             Fol "andFol" Fol [left, function]
           | Fol "orFol"  Fol [left, function]
           > left:
             "forall"  Set "." Fol [binder, function]
           | "exists"  Set "." Fol [binder, function]

  syntax String ::= "checkSat" "(" Fol ")" [function]
  syntax String ::= "SMTLibQuery" "(" Fol ")" [function, klabel(SMTLibQuery)]

  rule B1:Bool andFol B2:Bool => B1 andBool B2 [anywhere]
  rule B1:Bool orFol  B2:Bool => B1 orBool  B2 [anywhere]
  rule notFol B:Bool => notBool B [anywhere]
endmodule
