// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module ISSUE
  syntax Bool ::= "isMap4Subst" "(" Map ")" [function]
  rule isMap4Subst(I:Int |-> A:K) => true [anywhere]
endmodule
