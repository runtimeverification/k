module FOL
  syntax Fol ::= Bool
               | "notFol" Fol
               > left:
	         Fol "andFol" Fol [left]
	       | Fol "orFol"  Fol [left]
	       > "(" "forall" "(" IntList ")" "(" Bool ")" ")"

  syntax IntList ::= List{Int, ";"}


  rule B1:Bool andFol B2:Bool => B1 andBool B2 [anywhere]
  rule B1:Bool orFol  B2:Bool => B1 orBool  B2 [anywhere]
  rule notFol B:Bool => notBool B [anywhere]

endmodule