// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST
  imports INT
  imports BOOL
  imports ML-SYNTAX

  configuration <k> $PGM:K </k> <c> 0 </c>

  syntax KItem ::= "foo" | "bar" | "baz" | test(K) | test2(K, K) | test3(K, Int) | stuff(K)
  rule foo #Or bar #Or baz => 0
  rule (.K => 2) ~> test(foo #Or bar)
  rule test(test2(baz,_) #Or test(test2(baz,_))) => 1
  rule stuff(test(test3(baz,V:Int) #Or test(test3(baz,V:Int)))) => V

  syntax KItem ::= "macro"
  rule macro => a #Or b [macro]
  syntax Foo ::= "a"
  syntax Bar ::= "b"
  rule <k> macro ... </k>  <c> 0 => 1 </c>

endmodule
