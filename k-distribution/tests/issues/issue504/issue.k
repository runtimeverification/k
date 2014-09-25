// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "builtins/symbolic-calculus.k"
module ISSUE
  imports SYMBOLIC-CALCULUS

  syntax S ::= "test"

  rule test => I:Int when fresh(I)

endmodule