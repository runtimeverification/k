// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"

module TEST
  imports LIST

  syntax List ::= init(Int)
                | initLeft(Int)   [function]
                | initRight(Int)  [function]
  rule init(N) => initLeft(N) initRight(N)
  rule initLeft(N) => initLeft(N -Int 1) ListItem(N)
  when N >=Int 0
  rule initLeft(N) => .List
  when N <Int 0
  rule initRight(N) => ListItem(N) initRight(N -Int 1)
  when N >=Int 0
  rule initRight(N) => .List
  when N <Int 0
endmodule

