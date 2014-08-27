// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "basic-exp.k"
require "bool.k"
require "int.k"

module EXP-SYNTAX
  imports BASIC-EXP-SYNTAX
  imports BOOL-EXP-SYNTAX
  imports INT-EXP-SYNTAX
// Basic arithmetic and boolean operations;
  syntax Exp ::= Exp "*" Exp   [mul, left, strict]       // multiplication
             | Exp "/" Exp   [div, left, strict]       // division
             > left:
               Exp "+" Exp   [plus, left, strict]       // addition
             > non-assoc:
               Exp "<=" Exp  [leq, latex({#1}\leq{#2}), seqstrict]
             | Exp "==" Exp  [eq, strict]                   // equality test

             > "not" Exp   [not, strict]                   // boolean negation
             > left:
               Exp "and" Exp [and, strict(1)]    // boolean conjunction
endmodule

module EXP imports EXP-SYNTAX
  imports BOOL-EXP
  imports INT-EXP
  rule  I1:Int + I2:Int => I1 +Int I2
  rule  I1:Int * I2:Int => I1 *Int I2
  rule  I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule  I1:Int <= I2:Int => I1 <=Int I2
  rule  V1:Val == V2:Val => V1 ==K V2
  rule  not T:Bool => notBool T
  rule  true and E:Exp => E
  rule  false and E => false
endmodule
