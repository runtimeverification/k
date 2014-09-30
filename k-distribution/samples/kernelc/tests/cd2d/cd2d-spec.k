// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module CD2D-SPEC

  syntax Float ::= "E_sqv" [function]
  rule E_sqv => 9.31322574615478515625E-10 //0x1.p-30

  syntax Float ::= "E_sqs" [function]
  rule E_sqs => 7.2759576141834259033203125E-12 //0x1.p-37

  syntax Float ::= "E_dot" [function]
  rule E_dot => 5.82076609134674072265625E-11 //0x1.p-34

  syntax Float ::= "E_tau" [function]
  rule E_tau => 4.76837158203125E-7 //0x1.p-21

  syntax Float ::= "E_hlos" [function]
  rule E_hlos => 1.4551915228366851806640625E-11 //0x1.p-36

  syntax Float ::= "VE_MAX" [function]
  rule VE_MAX => 1200.0

  syntax Float ::= "DS_MAX" [function]
  rule DS_MAX => 100.0

  syntax Float ::= "D" [function]
  rule D => 5.0

  syntax Bool ::= DISTANCE(Float) [function]
  rule DISTANCE(X:Float) => (--Float DS_MAX) <=Float X andBool X <=Float DS_MAX

  syntax Bool ::= VELOCITY(Float) [function]
  rule VELOCITY(X:Float) => (--Float VE_MAX) <=Float X andBool X <=Float VE_MAX

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
