
//@ \subsection{Symbolic Integers}

module INT-SYM
//  imports INT
  imports BOOL-SYM
/*@
  This module is designed with a minimal support. 
*/

/*@ 
  Symbolic integer values:
*/

  syntax IntSymVar ::= "symInt" "(" Id ")" 

/*@
  Any symbolic integer is of sort Int:
*/

  syntax Int ::= IntSymVar

/*@
  The predicate defining the symbolic integer expressions.
*/
  syntax Bool ::= "isIntSymExp" "(" K ")" 
 
  rule isIntSymExp(I1:Int +Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int +Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

 
  rule isIntSymExp(I1:Int -Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int -Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int *Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int *Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int /Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int /Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]


  rule isIntSymExp(K:K) => true
       when 'isIntSymVar(K) ==K true
       [anywhere]

/*@
  Extending Int with symbolic expressions:
*/
  rule 'isInt(K:K) => true
       when isIntSymExp(K) ==K true
       [anywhere]

  rule 'isInt(_:Int +Int _:Int) => true [anywhere]
  rule 'isInt(_:Int *Int _:Int) => true [anywhere] 
  rule 'isInt(_:Int /Int _:Int) => true [anywhere]

/*@
  Symbolic integer expressions extend the symbolic boolean
  expressions:
*/

  rule isBoolSymExp(I1:Int <=Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int <=Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int ==Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int ==Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

//@ Some simplification rules.

  rule (I:Int ==Int I:Int) => true [anywhere]

  rule (I:Int *Int I +Int I +Int I +Int 1)
       => 
       (I +Int 1) *Int (I +Int 1)
       [anywhere]

  rule I:Int <=Int I:Int => true [anywhere] 

/*
  rule I1:Int <=Int (I2:Int +Int I:Int) => true
       when I >=Int 0
       [anywhere]

  rule I1:Int <=Int (I2:Int +Int I:Int) => false
       when I <Int 0
       [anywhere]
*/


  rule ((I1:Int ==Int I2:Int *Int I2) andBool (I3:Int ==Int I2))
       impliesBool
       ((I:Int +Int I1) ==Int (I +Int I3 *Int I3))
       =>
       true
       [anywhere]

endmodule 


