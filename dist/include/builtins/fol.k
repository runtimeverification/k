module FOL
  syntax Fol ::= Bool
               | Fol "andFol" Fol
	       | Fol "orFol"  Fol
               | "notFol" Fol

  rule B1:Bool andFol B2:Bool => B1 andBool B2 [anywhere]
  rule B1:Bool orFol  B2:Bool => B1 orBool  B2 [anywhere]
  rule notFol B:Bool => notBool B [anywhere]
endmodule