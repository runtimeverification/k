// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "int.k"

module COUNTER-HOOKS
  imports #COUNTER-INTERFACE
  imports INT-HOOKS

  syntax Int ::= #distinctCounter(Int)  [function,
                    hook(#COUNTER:distinctCounter)]
               | "#counter"             [function]
  rule #counter => #distinctCounter(0)
endmodule
