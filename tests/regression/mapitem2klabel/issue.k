
module ISSUE
  syntax Bool ::= "isMap4Subst" "(" Map ")" [function]
  rule isMap4Subst(I:Int |-> A:K) => true [anywhere]
endmodule
