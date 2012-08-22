module EXP-SYNTAX
// Basic arithmetic and boolean operations;
  syntax K ::= Bool | Int 
             | "(" K ")" [bracket]
             > left: 
               K "*" K   [left, strict]       // multiplication
             | K "/" K   [left, strict]       // division
             > left:
               K "+" K   [left, strict]       // addition
             > non-assoc:
               K "<=" K  [latex({#1}\leq{#2}), seqstrict]
             | K "==" K  [strict]                   // equality test

             > "not" K   [strict]                   // boolean negation
             > left: 
               K "and" K [strict(1)]    // boolean conjunction
endmodule

module EXP imports EXP-SYNTAX
  syntax KResult ::= Bool | Int 
  rule  I1:Int + I2:Int => I1 +Int I2  
  rule  I1:Int * I2:Int => I1 *Int I2  
  rule  I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0  
  rule  I1:Int <= I2:Int => I1 <=Int I2  
  rule  V1:KResult == V2:KResult => V1 ==K V2  
  rule  not T:Bool => notBool T  
  rule  true and E:K => E  
  rule  false and E => false  
endmodule
