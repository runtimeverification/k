module EXP
  // Basic arithmetic and boolean operations;
  syntax K ::= K "+" K   [gather(E e), prec(33), strict]       // addition
             | K "*" K   [gather(E e), prec(31), strict]       // multiplication
             | K "/" K   [gather(E e), prec(31), strict]       // division
             | K "<=" K  [prec(37), latex("{#1}\leq{#2}"), seqstrict]
             | K "==" K  [prec(37), strict]                   // equality test
             | "not" K   [prec(53), strict]                   // boolean negation
             | K "and" K [gather(E e), prec(55), strict(1)]    // boolean conjunction
  syntax KResult ::= Bool | Int 

  rule  I1:Int + I2:Int => I1 +Int I2  
  rule  I1 * I2 => I1 *Int I2  
  rule  I1 / I2 => I1 /Int I2  when I2 =/=Int 0  
  rule  I1 <= I2 => I1 <=Int I2  
  rule  V1:KResult == V2:KResult => V1 ==K V2  
  rule  not T:Bool => notBool T  
  rule  true and E:K => E  
  rule  false and E => false  
endmodule
