require "builtins/map.k"

module TEST
  imports MAP

  syntax MyMap ::= init(Int)  [function]
  rule init(N) => N |-> 0, init(N -Int 1)
  when N >=Int 0
  rule init(N) => .MyMap
  when N <Int 0
endmodule

