// Copyright (c) 2020 K Team. All Rights Reserved.

module ABS-SPEC
  imports IMP

rule
  <threads><thread>...
    <k>
      if (0 <= a) {
        b = a;
      } else {
        b = 0 - a;
      }
    =>
      .K
    ...</k>
    <env>...
      a |-> LA:Int
      b |-> LB:Int
    ...</env>
  ...</thread></threads>
  <store>...
    LA |-> A:Int
    LB |-> (_ => absInt(A))
  ...</store>

endmodule
