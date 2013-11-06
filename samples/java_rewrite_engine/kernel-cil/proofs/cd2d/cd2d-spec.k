require "../../extended-float.k"

module CD2D-SPEC
  imports EXTENDED-FLOAT
  syntax Float ::= "E_sqv" [function]
  rule E_sqv => 0x1.p-30
  
  syntax Float ::= "VE_MAX" [function]
  rule VE_MAX => 1200.0

  syntax Bool ::= VELOCITY(Float) [function]
  rule VELOCITY(X:Float) => (--Float VE_MAX) <=Float X <=Float VE_MAX

  syntax Float ::= sqR(Float,Float) [function]
  rule sqR(X:Float, Y:Float) => X *Float X +Float Y *Float Y
endmodule
