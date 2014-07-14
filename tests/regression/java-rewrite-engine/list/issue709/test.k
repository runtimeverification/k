// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST

  syntax KItem ::= foo(List, List)
                 | start(Int)

  syntax Bool ::= isEmptyList(List) [function]

  rule isEmptyList(.List) => true

  rule start(I) => foo(ListItem(I),.List)
  
  rule foo((L => .List), (.List => L)) when isEmptyList(L) =/=K true [structural]
  
  rule foo(.List, L) => L

endmodule
