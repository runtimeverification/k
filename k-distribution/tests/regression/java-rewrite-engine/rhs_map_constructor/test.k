// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/map.k"

module TEST
  imports MAP

  syntax Map ::= init(Int)  [function]
  rule init(N) => N |-> 0 init(N -Int 1)
  when N >=Int 0
  rule init(N) => .Map
  when N <Int 0
endmodule

