// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "int.k"

module RANDOM-HOOKS
  imports INT-HOOKS

  syntax Int ::= "randomRandom" "(" Int ")" [function, klabel(randomRandom), hook(#RANDOM:randomRandom)]

endmodule
