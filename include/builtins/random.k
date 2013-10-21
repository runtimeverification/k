require "int.k"

module RANDOM-HOOKS
  imports #RANDOM-INTERFACE
  imports INT-HOOKS
  
  syntax Int ::= "randomRandom" "(" Int ")" [function, klabel(randomRandom), hook(#RANDOM:randomRandom)]

endmodule
