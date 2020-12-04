require "substitution.md"

module A

imports INT
imports SUBSTITUTION

syntax Int ::= KVar
syntax Bool ::= forall(KVar, IntList, Bool) [binder, function, smt-hook((forall ((#1 Int)) (=> (inI #1 #2) #3)))]
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true

syntax IntList ::= List{Int,""}
syntax Bool ::= Int "inI" IntList [function, smtlib(inI)]

syntax KItem ::= foo(IntList)
rule foo(_L) => 0

syntax KItem ::= bar(IntList, IntList)
rule bar(_L1, _L2) => 0

syntax KVar ::= "x" [token]
              | "y" [token]

endmodule
