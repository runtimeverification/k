// Copyright (c) 2012-2018 K Team. All Rights Reserved.

requires "unification.k"

module TEST
  imports K-REFLECTION
  imports MATCHING
  imports UNIFICATION

  syntax A ::= "a" 
             | "a1"
             | "a2"
             | foo(A, A)
  syntax B ::= "b"
             | "b1"
             | "b2"
  rule <k> a1 => b1 </k>
  rule <k> a2 => b2 </k>
 
  syntax K ::= assertEqual(K, K)
  rule assertEqual(K:K, K:K) => .

  syntax Test ::= "test"
  rule
    test  
  =>
    assertEqual(#getTerm(a /\ T), a)
    ~> assertEqual(#getConstraint(a /\ (?B:B === b)), ?B:B === b)
    ~> assertEqual(
        #getSubstitution(
          #getConstraint((?B:B /\ ((?B:B === ?B1:B) /\ (?B1:B === b1))) /\ (?B2:B === b2))),
        (?B:B |-> b1 ?B1:B |-> b1 ?B2:B |-> b2))
    ~> assertEqual(
        #match(
          foo(?A:A, a) /\ ((?A:A =/=K a1) === true),
          foo(?A1:A, ?A2:A) /\ (((?A1:A =/=K a1) === true) /\ (((?A2:A =/=K a2) === true)))),
        SetItem(?A1:A |-> ?A:A ?A2:A |-> a))
    ~> assertEqual(
        #unify(foo(?A1:A, a2) /\ T, foo(a1, ?A2:A) /\ T),
        SetItem((?A1:A === a1) /\ (?A2:A === a2)))
    ~> assertEqual(#rewrite(<k> a1 </k> /\ T), SetItem(<k> b1 </k> /\ T))
    ~> assertEqual(#rewrite(<k> b1 </k> /\ T), .Set)
    ~> assertEqual(
        #narrow(<k> ?A:A </k> /\ T),
        SetItem(<k> b1 </k> /\ (?A:A === a1)) SetItem(<k> b2 </k> /\ (?A:A === a2)))   
  configuration <k> $PGM:Test </k>
endmodule
