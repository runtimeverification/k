// Copyright (c) 2016 K Team. All Rights Reserved.

module SUM-SPEC
  imports IMP
rule
  <k>
    while (!(n <= 0)) {
      sum = sum + n;
      n = n + -1;
    }
  =>
    .K
  ...</k>
  <state>...
    n   |-> (N:Int => 0)
    sum |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2))
  ...</state>
requires N >=Int 0

rule
  <k>
    int n, sum;
    n = N:Int;
    sum = 0;
    while (!(n <= 0)) {
      sum = sum + n;
      n = n + -1;
    }
  =>
    .K
  </k>
  <state>
    .Map
  =>
    n   |-> 0
    sum |-> ((N +Int 1) *Int N /Int 2)
  </state>
requires N >=Int 0
endmodule
