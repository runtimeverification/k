// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module SUM-ITERATIVE-SPEC
  imports KERNELC

rule
  <k>
    while (n > 0) {
      s = s + n;
      n = n - 1;
    }
  =>
    .K
  ...</k>
  <env>...
    n |-> tv(int *, object(P1:Int))
    s |-> tv(int *, object(P2:Int))
  ...</env>
  <heap>...
    object(P1) |-> tv(int, N:Int => 0)
    object(P2) |-> tv(int, S:Int => S +Int ((N +Int 1) *Int N /Int 2))
  ...</heap>
requires N >=Int 0

rule
  <fun>... FUN:Map ...</fun>
  <k>
    sum_iterative(tv(int, N:Int))
  =>
    tv(int, (N +Int 1) *Int N /Int 2)
  ...</k>

endmodule
