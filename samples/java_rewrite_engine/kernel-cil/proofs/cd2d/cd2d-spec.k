// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "../../extended-float.k"

module CD2D-SPEC
  imports EXTENDED-FLOAT

//  rule F:Float ==Float F => true
//  rule F:Float =/=Float F => false

  syntax Bool ::=  "absFloat" "(" Float ")" "<=Float" Float [function]
  rule absFloat(X:Float) <=Float Y:Float => --Float Y <=Float X <=Float Y

  syntax Float ::=  dmax(Float, Float) [function]
  rule dmax(X:Float, Y:Float) => #if X <=Float Y #then Y #else X #fi

  syntax Float ::=  dmin(Float, Float) [function]
  rule dmin(X:Float, Y:Float) => #if X <=Float Y #then X #else Y #fi

  syntax Float ::= "E_sqv" [function]
  rule E_sqv => 0x1.p-30

  syntax Float ::= "E_sqs" [function]
  rule E_sqs => 0x1.p-37

  syntax Float ::= "E_dot" [function]
  rule E_dot => 0x1.p-34

  syntax Float ::= "E_tau" [function]
  rule E_tau => 0x1.p-21

  syntax Float ::= "E_hlos" [function]
  rule E_hlos => 0x1.p-36

  syntax Float ::= "VE_MAX" [function]
  rule VE_MAX => 1200.0

  syntax Float ::= "DS_MAX" [function]
  rule DS_MAX => 100.0

  syntax Float ::= "D" [function]
  rule D => 5.0

  syntax Bool ::= DISTANCE(Float) [function]
  rule DISTANCE(X:Float) => (--Float DS_MAX) <=Float X <=Float DS_MAX

  syntax Bool ::= VELOCITY(Float) [function]
  rule VELOCITY(X:Float) => (--Float VE_MAX) <=Float X <=Float VE_MAX

  syntax Float ::= sqR(Float,Float) [function]
  rule sqR(X:Float, Y:Float) => X *Float X +Float Y *Float Y

  syntax Float ::= dotR(Float,Float,Float,Float) [function]
  rule dotR(Ax:Float, Ay:Float, Bx:Float, By:Float)
    => Ax *Float Bx +Float Ay *Float By

  syntax Float ::= tauR(Float, Float, Float, Float, Float, Float) [function]
  rule tauR(Ux:Float, Uy:Float, Vx:Float, Vy:Float, B:Float, T:Float) =>
    dmin(dmax(B *Float sqR(Vx,Vy), --Float dotR(Ux,Uy, Vx, Vy)), T *Float sqR(Vx, Vy))

  syntax Bool ::= horizontalLosR(Float, Float, Float) [function]
  rule horizontalLosR(Sx,Sy,D) => sqR(Sx,Sy) <=Float D *Float D
endmodule
