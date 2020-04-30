require "substitution.k"

module A

imports INT
imports SUBSTITUTION

syntax IMap ::= IMap "[" Int "<-" Int "]" [function, klabel(storeI),  smtlib(storeI)]
syntax Int  ::= IMap "[" Int "]"          [function, klabel(selectI), smtlib(selectI)]
rule ( M:IMap [ K1 <- V ] ) [ K2 ] => V        requires K1  ==Int K2
rule ( M:IMap [ K1 <- V ] ) [ K2 ] => M [ K2 ] requires K1 =/=Int K2

syntax Bool ::= forall(KVar, Int, Int, Bool) [binder, function, smtlib((forall ((#1 Int)) (=> (and (>= #1 #2) (< #1 #3)) #4)))]
rule forall(X, LB, UB, E) => E[LB / X] andBool forall(X, LB +Int 1, UB, E) requires LB  <Int UB
rule forall(_, LB, UB, _) => true                                          requires LB >=Int UB

syntax Int ::= KVar
syntax KVar ::= "x" [token]

syntax KItem ::= validateSignatures(Int, Int, IMap, IMap)
rule validateSignatures(I, N, Keys, Signatures)
  => validateSignature(I, Keys, Signatures)
  ~> validateSignatures(I +Int 1, N, Keys, Signatures)
     requires I <Int N
rule validateSignatures(I, N, _, _) => . requires I >=Int N

syntax KItem ::= validateSignature(Int, IMap, IMap)
rule validateSignature(I, Keys, Signatures)
  => #if sign(SALT, Keys[I]) ==Int Signatures[I]
     #then .
     #else #bottom
     #fi

syntax Int ::= sign(Int, Int) [function, smtlib(sign)]

syntax Int ::= "SALT" [function]
rule SALT => 7 [macro]

syntax KItem ::= "#bottom"

endmodule
