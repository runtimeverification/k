require "int.k"

module ARRAY-SYNTAX
  syntax Array ::= // store(array, index, value)
  	       	   "store"       "(" K "," K "," K ")"  [smtlib(store)]
  	       	   // const-array(name, min, max, initial value)
		 | "const-array" "(" Id "," K "," K "," K ")" 
		 
  syntax K ::= // select(array, index)
  	       "select" "(" K "," K ")"  [function, smtlib(select)]

  syntax Int ::= "size-of-array" "(" Array ")"

  syntax K ::= K "<=K" K [function]
  syntax K ::= K "<K"  K [function]
  syntax K ::= K "-K"  K [function]
  syntax K ::= K "!=K" K [function]  

endmodule


module ARRAY
  imports ARRAY-SYNTAX
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  // Int can be used as an index by default; the below rules should be added 
  // for each type used as an index
  
  /* hacks */
  rule I:Int <=K J:Int => I <=Int J
  rule I:Int <K J:Int  => I <Int  J
  rule I:Int -K J:Int  => I -Int  J
  
  rule I:Int !=K J:Int => I =/=Int J
  rule I:Int =K J:Int => I ==Int J
  rule isInt(select(A:Array, I:K)) => true when isSymbolicInt(I) [anywhere]

  rule I:Bool !=K J:Bool => I =/=Bool J
  rule I:Bool =K J:Bool => I ==Bool J
  rule isBool(select(A:Array, I:K)) => true when isSymbolicInt(I) [anywhere]

  rule I:String !=K J:String => I =/=String J
  rule I:String =K J:String => I ==String J
  rule isString(select(A:Array, I:K)) => true when isSymbolicInt(I) [anywhere]
  /* end hacks */


  // main array axioms
  rule select(store(A:K, I:K, V:K), I:K) => V
  rule select(store(A:K, I:K, V:K), J:K) => select(A, J)
       when I !=K J

  // select from constant array
  rule select(const-array(_:Id, MIN:K, MAX:Int, V:K), I:Int) => V
       when (MIN <=K I) andBool (I <K MAX)

  // simplification of multiple store
  rule store(store(A:K, I:K, V:K), J:Int, V':K)
       =>
       store(store(A, J, V':K), I, V)
       when J <K I
       [anywhere]

  rule store(store(A:K, I:K, _), I, V:K)
       =>
       store(A, I, V)
       [anywhere]   

  // array size
  rule size-of-array(store(A:K, I:K, V:K)) => size-of-array(A) [anywhere]
  rule size-of-array(const-array(_:Id, MIN:K, MAX:K, _:K)) => MAX -K MIN [anywhere]

endmodule
