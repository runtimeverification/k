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

  rule (S1 SetItem(E)) -Set S2 =>  S1 -Set S2             requires         E in S2 andBool notBool E in S1 [simplification]
  rule S1 -Set (S2 SetItem(E)) =>  S1 -Set S2             requires notBool E in S1 andBool notBool E in S2 [simplification]

endmodule
