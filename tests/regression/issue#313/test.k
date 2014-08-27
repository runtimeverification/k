// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module TEST
  syntax KLabel ::= "#foo" [function]
  syntax K ::= foo(K)  [function, klabel(#foo)]
  rule #foo(1) => 0
endmodule
