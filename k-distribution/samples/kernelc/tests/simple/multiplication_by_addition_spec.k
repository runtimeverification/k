// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module MULTIPLICATION-BY-ADDITION-SPEC
  imports KERNELC

rule
  <fun>... FUN:Map ...</fun>
  <k>
    multiplication_by_addition(tv(int, X:Int), tv(int, Y:Int))
  =>
    tv(int, X *Int Y)
  ...</k>

endmodule
