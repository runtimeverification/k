// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "smt.k"
require "fol.k"

//@ \subsection{Symbolic Calculus}
module SYMBOLIC-CALCULUS-SYNTAX
//  imports BOOL-SYMBOLIC-SYNTAX
//  imports INT-SYMBOLIC-SYNTAX
endmodule

module SYMBOLIC-CALCULUS
  imports SYMBOLIC-CALCULUS-SYNTAX
//  imports BOOL-SYMBOLIC
//  imports INT-SYMBOLIC
  imports SMT-HOOKS
  imports FOL

/*@
  The following function is used to generate fresh names for symbolic values.
*/
//  syntax Id ::= "fresh" "(" Int ")" [function]
//  rule fresh(I:Int) => String2Id("symVar" +String Int2String(I)) [anywhere]


/*@
  The following defines the substitution of the symbolic values with
  symbolic expressions.
  This should be defined in a more generic way using ASTs.
*/

  syntax KItem ::= KItem "[" KItem "/" KItem "]"

  rule (F1:K andBool F2:K) [ V:K / X:K ]
        =>
        (F1 [ V:K / X:K ]) andBool (F2[ V:K / X:K ])
        [anywhere]

  rule (notBool F:K) [ V:K / X:K ]
        =>
        notBool (F[ V:K / X:K ])
        [anywhere]


  rule (I1:Int <=Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) <=Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int ==Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) ==Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int +Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) +Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int *Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) *Int (I2 [ E1 / E2 ])
       [anywhere]

  rule I:Int [ E1:K / E2:K ] => E1
       when I ==K E2
       [anywhere]

  rule I:Int [ E1:K / E2:K ] => I
       when I =/=K E2
       [anywhere]

  rule (I1:Int ==Int I2:Int) andBool F:K impliesBool B:K
       =>
       (F impliesBool (B [ I2 / I1 ]))
       [anywhere]

  rule (I1:Int ==Int I2:Int) impliesBool B:K
       =>
       B [ I2 / I1 ]
       [anywhere]

//@ satisfaction relation

  syntax #Bool ::= Bool "SMT|=" Bool  [function]

  rule B1:Bool SMT|= B2:Bool => true
       when checkSat(B1 andBool (notBool B2)) ==K "unsat"
       [anywhere]
endmodule

