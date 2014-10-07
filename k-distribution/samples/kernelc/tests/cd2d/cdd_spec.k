// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module CDD-SPEC
  imports KERNELC

rule [max-spec]:
  <fun>... FUN:Map ...</fun>
  <k>
    max(tv(double, X:Float{exponent(11), significand(53)}), tv(double, Y:Float{exponent(11), significand(53)}))
  =>
    tv(double, Z:Float{exponent(11), significand(53)})
  ...</k>
requires notBool isNaN(X) andBool notBool isNaN(Y)
ensures Z ==Float maxFloat(X, Y)

rule [min-spec]:
  <fun>... FUN:Map ...</fun>
  <k>
    min(tv(double, X:Float{exponent(11), significand(53)}), tv(double, Y:Float{exponent(11), significand(53)}))
  =>
    tv(double, Z:Float{exponent(11), significand(53)})
  ...</k>
requires notBool isNaN(X) andBool notBool isNaN(Y)
ensures Z ==Float minFloat(X, Y)

rule [sqs-spec]:
  <fun>... FUN:Map ...</fun>
  <k>
    sqs(tv(double, X:Float{exponent(11), significand(53)}), tv(double, Y:Float{exponent(11), significand(53)}))
  =>
    tv(double, Z:Float{exponent(11), significand(53)})
  ...</k>
requires minusInfinity(11,53) <Float X andBool X <Float plusInfinity(11,53) andBool minusInfinity(11,53) <Float Y andBool Y <Float plusInfinity(11,53)
ensures Z ==Float X *Float X +Float Y *Float Y

rule [dot-spec]:
  <fun>... FUN:Map ...</fun>
  <k>
    dot(tv(double, Ux:Float{exponent(11), significand(53)}), tv(double, Uy:Float{exponent(11), significand(53)}), tv(double, Vx:Float{exponent(11), significand(53)}), tv(double, Vy:Float{exponent(11), significand(53)}))
  =>
    tv(double, Z:Float{exponent(11), significand(53)})
  ...</k>
requires isValidDistance(Ux) andBool isValidDistance(Uy) andBool
         isValidVelocity(Vx) andBool isValidVelocity(Vy)
ensures Z ==Float Ux *Float Vx +Float Uy *Float Vy

endmodule
