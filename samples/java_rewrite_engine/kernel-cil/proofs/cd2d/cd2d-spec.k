require "../../extended-float.k"

module CD2D-SPEC
  imports EXTENDED-FLOAT
  syntax Float ::= "E_sqv" [function]
  rule E_sqv => 0x1.p-30

  syntax Float ::= "E_sqs" [function]
  rule E_sqs => 0x1.p-37

  syntax Float ::= "VE_MAX" [function]
  rule VE_MAX => 1200.0
  
  syntax Float ::= "DS_MAX" [function]
  rule DS_MAX => 100.0

  syntax Bool ::= DISTANCE(Float) [function]
  rule DISTANCE(X:Float) => (--Float DS_MAX) <=Float X <=Float DS_MAX

  syntax Bool ::= VELOCITY(Float) [function]
  rule VELOCITY(X:Float) => (--Float VE_MAX) <=Float X <=Float VE_MAX

  syntax Float ::= sqR(Float,Float) [function]
  rule sqR(X:Float, Y:Float) => X *Float X +Float Y *Float Y

  syntax Float ::=  "absFloat" "(" Float ")" "<=Float" Float [function]
  rule absFloat(X:Float) <=Float Y:Float => --Float Y <=Float X <=Float Y

endmodule
