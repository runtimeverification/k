// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST
  syntax KItem ::= foo(K, KLabel) [function]
                 | "k1" [function]
                 | "k2" [function]
                 | "k3" [function]
  syntax KLabel ::= "l"
  syntax KList ::= bar(K) [function]
  rule foo(K:K, KL:KLabel) => KL(bar(K))
  rule bar(KI:KItem ~> K:K) => KI,,bar(K)
  rule bar(.K) => .KList
  rule k1 => 1 ~> 2 ~> 3
  rule k2 => 0
  rule k3 => .K
endmodule

