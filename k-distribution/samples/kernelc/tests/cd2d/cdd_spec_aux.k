// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module CDD-SPEC-AUX

  syntax Float ::= "E_sqv" | "E_sqs" | "E_dot" | "E_tau" | "E_hlos"
                 | "VE_MAX" | "DS_MAX" | "D"

  rule E_sqv => 9.31322574615478515625E-10          [macro] //0x1.p-30
  rule E_sqs => 7.2759576141834259033203125E-12     [macro] //0x1.p-37
  rule E_dot => 5.82076609134674072265625E-11       [macro] //0x1.p-34
  rule E_tau => 4.76837158203125E-7                 [macro] //0x1.p-21
  rule E_hlos => 1.4551915228366851806640625E-11    [macro] //0x1.p-36
  rule VE_MAX => 1200.0                             [macro]
  rule DS_MAX => 100.0                              [macro]
  rule D => 5.0                                     [macro]

  syntax Bool ::= isValidDistance(Float) [function]
  rule isValidDistance(X:Float) => (--Float DS_MAX) <=Float X andBool X <=Float DS_MAX

  syntax Bool ::= isValidVelocity(Float) [function]
  rule isValidVelocity(X:Float) => (--Float VE_MAX) <=Float X andBool X <=Float VE_MAX

  syntax Float ::= sqR(Float, Float) [function]
  rule sqR(X:Float, Y:Float) => X *Float X +Float Y *Float Y

  syntax Float ::= dotR(Float,Float,Float,Float) [function]
  rule dotR(Ax:Float, Ay:Float, Bx:Float, By:Float)
    => Ax *Float Bx +Float Ay *Float By

  syntax Bool ::= horizontalLosR(Float, Float, Float) [function]
  rule horizontalLosR(Sx, Sy, D) => sqR(Sx, Sy) <=Float D *Float D

  syntax Float ::= tauR(Float, Float, Float, Float) [function]
  rule tauR(Ux:Float, Uy:Float, Vx:Float, Vy:Float) =>
    minFloat(maxFloat(0.0 *Float sqR(Vx, Vy), --Float dotR(Ux, Uy, Vx, Vy)), 300.0 *Float sqR(Vx, Vy))

  syntax Float ::= omegaR(Float, Float, Float, Float) [function]
  rule omegaR(Ux:Float, Uy:Float, Vx:Float, Vy:Float) =>
    sqR(Vx, Vy) *Float sqR(Ux, Uy) +Float 2.0 *Float tauR(Ux, Uy, Vx, Vy) *Float dotR(Ux, Uy, Vx, Vy) +Float tauR(Ux, Uy, Vx, Vy) *Float tauR(Ux, Uy, Vx, Vy) -Float 5.0 *Float 5.0 *Float sqR(Vx, Vy)
endmodule
