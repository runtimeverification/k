// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "long.k"

module TIME-HOOKS
  imports #TIME-INTERFACE
  imports LONG-HOOKS

  syntax Long ::= "time" "(" ")" [function, klabel(randomRandom), hook(#TIME:time)]

endmodule
