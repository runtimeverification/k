// Copyright (c) 2014 K Team. All Rights Reserved.
require "map.k"

module MAP-IMPL
  imports MAP

  // syntax K ::= Map "[" K "]"
  rule (K1:K |-> K2:K _:Map)[K1] => K2

  // syntax Map ::= Map "[" K "<-" K "]"
  rule (K1:K |-> _ M:Map)[K1 <- K2:K] => K1 |-> K2 M
  rule M:Map[K1:K <- K2:K] => K1 |-> K2 M
  when notBool(K1 in keys(M))

  // syntax Map ::= Map "[" K "<-" "undef" "]"
  rule (K:K |-> _ M:Map)[K <- undef] => M

  // syntax Map ::= Map "-Map" Map
  // TODO(AndreiS): the rules below do not work properly
  rule (K1:K |-> K2:K M1:Map) -Map M2:Map
    => #if K2 ==K M2[K1] #then M1 -Map M2 #else K1 |-> K2 (M1 -Map M2) #fi
  rule .Map -Map _:Map => .Map

  // syntax Map ::= updateMap(Map, Map)
  rule updateMap(M1:Map, K1:K |-> K2:K M2:Map) => updateMap(M1[K1 <- K2], M2)
  rule updateMap(M:Map, .Map) => M

  // syntax Set ::= keys(Map)
  rule keys(K:K |-> _ M:Map) => SetItem(K) keys(M)
  rule keys(.Map) => .Set

  // syntax List ::= values(Map)
  rule values(_ |-> K:K M:Map) => ListItem(K) values(M)
  rule values(.Map) => .List

  // syntax Int ::= size(Map)
  rule size(_ |-> _ M:Map) => 1 +Int size(M)
  rule size(.Map) => 0

  // syntax Bool ::= Map "<=Map" Map
  rule (K1:K |-> K2:K M1:Map) <=Map (K1 |-> K2 M2:Map) => M1 <=Map M2
  rule .Map <=Map _:Map => true
endmodule

