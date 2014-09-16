// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module SUM-RECURSIVE-SPEC
  imports KERNELC

rule
  <fun>... FUN:Map ...</fun>
  <k>
    sum_recursive(tv(int, N:Int))
  =>
    tv(int, (N +Int 1) *Int N /Int 2)
  ...</k>
requires N >=Int 0

endmodule
