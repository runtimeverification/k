// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST
  syntax Int ::= foo(Int)   [function]
               | bar(Int)   [function]
  configuration <k> $PGM ~> bar(0) </k>
  rule foo(0) => 0
  rule foo(N) => N +Int 1
  rule bar(_) => foo(0)
endmodule

