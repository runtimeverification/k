// Copyright (c) 2014 K Team. All Rights Reserved.
require "builtins/set.k"
require "builtins/map.k"

module TEST
  imports SET
  imports MAP

  syntax Int ::= size(Set)    [function]
  rule size(SetItem(_) S:Set) => 1 +Int size(S)
  rule size(.Set) => 0

  syntax Set ::= setRange(Int)   [function]
  rule setRange(N) => SetItem(N) setRange(N -Int 1)
  when N >Int 0
  rule setRange(N) => .Set
  when N <=Int 0

  syntax Int ::= size(Map)    [function]
  rule size(_ |-> _ M:Map) => 1 +Int size(M)
  rule size(.Map) => 0

  syntax Map ::= mapRange(Int)   [function]
  rule mapRange(N) => N |-> 0 mapRange(N -Int 1)
  when N >Int 0
  rule mapRange(N) => .Map
  when N <=Int 0
endmodule

