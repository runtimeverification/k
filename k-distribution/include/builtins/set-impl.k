// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "set.k"


module SET-IMPL
  imports SET
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  // syntax Set ::= intersectSet(Set, Set)
  rule intersectSet(S1:Set, S2:Set) => S1 -Set (S1 -Set S2)

  // syntax Set ::= Set "-Set" Set
  rule (SetItem(K:K) S1:Set) -Set S2:Set
    => #if K in S2 ==K true #then S1 -Set S2 #else SetItem(K) (S1 -Set S2) #fi
  rule .Set -Set _:Set => .Set

  // syntax Bool ::= K "in" Set
  rule K1:K in SetItem(K2:K) _:Set => true requires K1 =K K2
  rule K1:K in SetItem(K2:K) S:Set => K1 in S requires notBool(K1 =K K2)
  rule _ in .Set => false

  // syntax Bool ::= Set "<=Set" Set
  rule S1:Set <=Set S2:Set => (S1 -Set S2) =K .Set

  // syntax Int ::= size(Set)
  rule size(SetItem(_) S:Set) => 1 +Int size(S)
  rule size(.Set) => 0
endmodule

