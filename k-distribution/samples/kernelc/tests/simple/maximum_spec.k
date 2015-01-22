// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module MAXIMUM-SPEC
  imports KERNELC

rule
  <fun>... FUN:Map ...</fun>
  <k>
    maximum(tv(int, X:Int), tv(int, Y:Int))
  =>
    tv(int, maxInt(X, Y))
  ...</k>

endmodule
