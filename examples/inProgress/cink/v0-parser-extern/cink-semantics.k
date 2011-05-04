kmod CINK-SEMANTICS is including K + PL-ID + PL-INT + PL-CONVERSION

  syntax KLabel ::= `Plus [strict]  // 2 args
                  | `Minus [strict]
                  | `Mult [strict]
                  | `Gt [strict]
                  | `Var

  /*@\subsubsection*{ASTs which are results.} */

  syntax Val ::= Int | void  
  syntax KResult ::= Val 

  /*@ \subsubsection*{Auxiliary constructs.} */

  syntax K ::= initial
             | restore ( Map )
             | endOfFunction
             | Id

//  rule initial => 0 [structural]

  configuration <T>
                  <k> .K </k>
                  <env> .Map </env>
                  <funs> .Map </funs> 
                  <in> .List </in>
//                  <out> "" </out> 
                </T>
  
  /*@\subsubsection*{Expressions Evaluation.} */

  rule Plus(I1:Int,, I2:Int) => _+Int_(I1,I2) [structural]
  rule Minus(I1,, I2) => _-Int_(I1,I2) [structural]
  rule Mult(I1,, I2) => I1 *Int I2 [structural]
  rule Gt(I1,, I2) => Bool2Int(I1 >Int I2) [structural]

//  rule <k> Var(X:Id) => I:Int <_/k> <env_> X |-> I <_/env> 

 syntax KLabel ::= test
 rule test => Plus(1,, 2) [structural]

endkm

