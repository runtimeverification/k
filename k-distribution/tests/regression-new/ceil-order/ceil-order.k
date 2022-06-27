// Copyright (c) 2022 K Team. All Rights Reserved.

module CEIL-ORDER
    imports SET
    imports INT
    imports K-EQUAL
    imports BOOL

  syntax KItem ::= step ( Set ) | done ( Set )
  rule <k> step ( Set ) => done ( Set ) </k>

  rule #Ceil(@S:Set SetItem(@E:KItem)) => {(@E in @S) #Equals false} #And #Ceil(@S) #And #Ceil(@E)
    [anywhere, simplification]

  rule intersectSet(_S, .Set) => .Set                                                              [simplification]
  rule intersectSet(.Set, _S) => .Set                                                              [simplification]
  rule intersectSet(S, S) => S                                                                     [simplification]
  rule intersectSet(S1 SetItem(E), S2) => intersectSet(S1, S2)            requires notBool E in S2 [simplification]
  rule intersectSet(S1, S2 SetItem(E)) => intersectSet(S1, S2)            requires notBool E in S1 [simplification]
  rule intersectSet(S1 SetItem(E1) SetItem(E2), S2) => intersectSet(S1 SetItem(E1), S2) SetItem(E2)
    requires E2 in S2                                        [simplification]
  rule intersectSet(S1, S2 SetItem(E1) SetItem(E2)) => intersectSet(S1, S2 SetItem(E1)) SetItem(E2)
    requires E2 in S1 andBool notBool E2 in (S2 SetItem(E1)) [simplification]

endmodule
