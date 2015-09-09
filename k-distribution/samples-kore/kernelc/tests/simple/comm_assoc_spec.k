// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "../../kernelc.k"

module COMM-ASSOC-SPEC
  imports KERNELC

rule
  <fun>... FUN:Map ...</fun>
  <k>
    comm_assoc(tv(int, X:Int), tv(int, Y:Int), tv(int, Z:Int))
  =>
    tv(int, 1)
  ...</k>

endmodule
