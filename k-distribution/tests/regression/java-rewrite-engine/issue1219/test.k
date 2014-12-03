// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST
  syntax Int ::= foo(Map) [function]
  rule foo((K1 |-> K2) M:Map) => foo(M)
  rule foo(.Map) => 0
endmodule

