// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST
  imports INT
  imports BOOL

  syntax KItem ::= "foo" | "bar" | "baz" | test(K) | test2(K, K)
  rule foo #Or bar #Or baz => 0
  rule (.K => 2) ~> test(foo #Or bar)
  rule test(test2(baz,_) #Or test(test2(baz,_))) => 1

endmodule
