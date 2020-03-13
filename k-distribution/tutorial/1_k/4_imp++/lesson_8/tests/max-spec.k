// Copyright (c) 2020 K Team. All Rights Reserved.

module MAX-SPEC
  imports IMP

rule
  <threads><thread>...
    <k>
      if (a > b) {
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
    LC |-> (_ => maxInt(A, B))
  ...</store>

endmodule
