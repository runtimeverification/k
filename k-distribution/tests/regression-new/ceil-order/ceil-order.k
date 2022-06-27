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

  rule intersectSet(S1 SetItem(E), S2) => intersectSet(S1, S2)
    requires notBool E in S2
    [simplification]

  rule intersectSet(S1, S2 SetItem(E)) => intersectSet(S1, S2)
    requires notBool E in S1 andBool notBool E in S2
    [simplification]

  rule E1 in (S SetItem(E2)) => E1 in S
    requires E1 =/=K E2
    [simplification]

endmodule
