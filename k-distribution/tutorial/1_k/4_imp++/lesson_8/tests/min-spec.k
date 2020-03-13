// Copyright (c) 2020 K Team. All Rights Reserved.

module MIN-SPEC
  imports IMP

rule
  <threads><thread>...
    <k>
      if (a <= b) {
        c = a;
      } else {
        c = b;
      }
    =>
      .K
    ...</k>
    <env>...
      a |-> LA:Int
      b |-> LB:Int
      c |-> LC:Int
    ...</env>
  ...</thread></threads>
  <store>...
    LA |-> A:Int
    LB |-> B:Int
    LC |-> (_ => minInt(A, B))
  ...</store>

endmodule
