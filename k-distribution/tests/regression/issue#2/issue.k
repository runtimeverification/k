// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE
  syntax Foo ::= foo(Int, Int)
  rule foo(A, B) => A +Int B
endmodule

