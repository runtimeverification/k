require "bool-sym.k"
require "int-sym.k"

//@ \subsection{Symbolic Calculus}

module SYMBOLIC-CALCULUS
  imports BOOL-SYM
  imports INT-SYM

/*@ 
  The following function is used to generate fresh names for symbolic values.
*/
  syntax Id ::= "fresh" "(" Int ")" [function] 
  rule fresh(I:Int) => String2Id("symVar" +String Int2String(I)) [anywhere]


/*@
  The following defines the substitution of the symbolic values with
  symbolic expressions.
*/

  syntax K ::= K "[" K "/" K "]"

  rule (F1:K andBool F2:K) [ V:K / X:K ]
        =>
        F1 [ V:K / X:K ] andBool F2[ V:K / X:K ]
        [anywhere]

  rule (I1:Int <=Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) <=Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int ==Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) ==Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int +Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) +Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int *Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) *Int (I2 [ E1 / E2 ])
       [anywhere]

  rule I:Int [ E1:K / E2:K ] => E1 
       when I ==K E2
       [anywhere]
 
  rule I:Int [ E1:K / E2:K ] => I
       when I =/=K E2
       [anywhere]

  rule (I1:Int ==Int I2:Int) andBool F:K impliesBool B:K
       =>
       F impliesBool B [ I2 / I1 ]
       [anywhere]

  rule (I1:Int ==Int I2:Int) impliesBool B:K
       =>
       B [ I2 / I1 ]
       [anywhere]

endmodule

