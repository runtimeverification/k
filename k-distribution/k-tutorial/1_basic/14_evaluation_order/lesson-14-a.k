module LESSON-14-A-SYNTAX
  imports UNSIGNED-INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Exp ::= Int
               | Bool
               > left:
                  Exp "/" Exp [strict]
               > left: 
                  Exp "+" Exp [strict]
               |  Exp "-" Exp [seqstrict]
               > left: Exp "&&" Exp [seqstrict]
endmodule

module LESSON-14-A
  imports LESSON-14-A-SYNTAX
  imports INT
  imports BOOL

  rule <k> I1:Int + I2:Int => I1 +Int I2 ...</k>
  rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k> requires I2 =/=Int 0
  rule <k> I1:Int - I2:Int => I1 -Int I2 ...</k>
  rule <k> B1:Bool && B2:Bool => B1 andBool B2 ...</k>

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_:Bool) => true
  rule isKResult(_) => false [owise]
endmodule
