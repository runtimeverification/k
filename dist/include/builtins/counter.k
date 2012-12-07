require "int.k"

module COUNTER-HOOKS
  imports #COUNTER-INTERFACE
  imports INT-HOOKS

  syntax Int ::= "#counter" [function, hook(#COUNTER:counter)]
endmodule
