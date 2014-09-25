// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module MINIMUM-SPEC
  imports KERNELC

rule
  <fun>... FUN:Map ...</fun>
  <k>
    minimum(tv(int, X:Int), tv(int, Y:Int))
  =>
    tv(int, minInt(X, Y))
  ...</k>

endmodule
