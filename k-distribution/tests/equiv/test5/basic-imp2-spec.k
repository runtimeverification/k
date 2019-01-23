// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module BASIC-IMP2-SPEC
imports IMP

syntax Id ::= "sum" [token]
            | "n" [token]

rule
  <k>
      sum = sum + n;
      n = n + 2;
  </k>
  <state>...
    sum |-> S:Int
    n   |-> N:Int
  ...</state>
requires N >=Int 0
ensures vars(ListItem(S) ListItem(N))

rule
  <k>
    .K
  </k>
  <state>...
    sum |-> S:Int
    n   |-> N:Int
  ...</state>
ensures vars(ListItem(S) ListItem(N))
 [trusted]



endmodule
