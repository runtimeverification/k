// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST

  syntax KItem ::= foo(List, List)
                 | test1(Int)
                 | test2(Int, Int)

  syntax Bool ::= isEmptyList(List) [function]
                | K "inList" List   [function]

  rule isEmptyList(.List) => true

  rule test1(I) => foo(ListItem(I),.List)

  rule foo((L => .List), (.List => L)) when isEmptyList(L) =/=K true [structural]

  rule foo(.List, L) => L

  rule test2(I1, I2) => I1 inList ListItem(I2)

  rule K:K inList .List => false
  rule K:K inList ListItem(K:K) _:List => true
  rule K:K inList ListItem(K1:K) L:List => K inList L when K =/=K K1

endmodule
