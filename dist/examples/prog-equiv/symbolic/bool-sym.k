//@ \subsection{Symbolic Booleans}

module BOOL-SYM
//  imports BOOL
/*@
  This module is designed with a minimal support. 
*/


/*@ 
  Symbolic integer values:
*/

  syntax BoolSymVar ::= "symBool" "(" Id ")" 

/*@
  The predicate defining the symbolic boolean expressions.
*/

  syntax Bool ::=  "isBoolSymExp" "(" K ")"

  rule isBoolSymExp(B:BoolSymVar) => true

  rule isBoolSymExp(B1:Bool andBool I2:Bool) => true
       when isBoolSymExp(B1) ==K true
       [anywhere]

  rule isBoolSymExp(B1:Bool orBool I2:Bool) => true
       when isBoolSymExp(B1) ==K true
       [anywhere]
/*@ 
  \textbf{Remark.~~}
  The symbolic boolean expressions are not sobsorted to Bool.
  This is a trick that help us to handle easier this expressions.
*/


  rule 'isBool(K:K) => true
       when isBoolSymExp(K) ==K true
       [anywhere]


//@ Some simplification rules.

  rule B:K impliesBool true => true  [anywhere]

  rule (B:K andBool B':K) impliesBool B => true  [anywhere]

  rule B:K andBool true => B  [anywhere]

  rule true andBool B:K => B  [anywhere]

  rule B:K orBool true => true  [anywhere]

  rule true orBool B:K => true  [anywhere]

  rule B:K impliesBool B => true [anywhere]


endmodule

