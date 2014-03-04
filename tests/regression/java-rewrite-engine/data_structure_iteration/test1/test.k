require "builtins/set.k"
require "builtins/map.k"

module TEST
  imports SET
  imports MAP

  syntax Int ::= size(MySet)    [function]
  rule size(MySetItem(_), S:MySet) => 1 +Int size(S)
  rule size(.MySet) => 0

  syntax MySet ::= setRange(Int)   [function]
  rule setRange(N) => MySetItem(N), setRange(N -Int 1)
  when N >Int 0
  rule setRange(N) => .MySet
  when N <=Int 0

  syntax Int ::= size(MyMap)    [function]
  rule size(_ |-> _, M:MyMap) => 1 +Int size(M)
  rule size(.MyMap) => 0

  syntax MyMap ::= mapRange(Int)   [function]
  rule mapRange(N) => N |-> 0, mapRange(N -Int 1)
  when N >Int 0
  rule mapRange(N) => .MyMap
  when N <=Int 0
endmodule

