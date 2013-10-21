require "int.k"

module COUNTER-HOOKS
  imports #COUNTER-INTERFACE
  imports INT-HOOKS

  syntax Int ::= #distinctCounter(Int)  [function, 
                    hook(#COUNTER:distinctCounter)]
               | "#counter"             [function]
  rule #counter => #distinctCounter(0)
endmodule
