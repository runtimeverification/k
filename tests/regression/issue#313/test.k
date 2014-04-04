// Copyright (C) 2012-2014 K Team. All Rights Reserved.

module TEST
  syntax KLabel ::= "#foo"
  syntax K ::= foo(K)  [function, klabel(#foo)]
  rule #foo(1) => 0
endmodule
