// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "domains.k"

module IMP-COMMON
  imports EMPTY-ID
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX

  syntax AExp  ::= Int | String | Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "if" "(" BExp ")"
                 | "while" "(" BExp ")" Block
                 | "print" "(" AExp ")" ";"   [strict]
                 | "halt" ";"
                 > Stmt Stmt                  [left]

  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}

  rule if (Cond) Block => if (Cond) Block else {} [macro]
endmodule

module IMP-SYNTAX
  imports ID
  imports IMP-COMMON
endmodule

module IMP
  imports INT
  imports BOOL
  imports STRING
  imports BASIC-K
  imports LIST
  imports MAP
  imports SET
  imports IMP-COMMON

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> `$PGM:Pgm`:K </k>
                  <state color="red"> .Map </state>
                </T>

// AExp

  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>

  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2

// BExp

  rule I1:Int <= I2:Int => I1 <=Int I2
  rule ! T:Bool => notBool T
  rule true && B => B
  rule false && _ => false

// Block

  rule {} => .K  [structural]
  rule {S} => S  [structural]

// Stmt

  rule <k> X = I:Int; => .K ...</k> <state>... X |-> `_ => I` ...</state>

  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]

  rule if (true)  S else _ => S
  rule if (false) _ else S => S

  rule while (B) S => if (B) {S while (B) S}  [structural]

// Pgm

  rule <k> int `X,Xs => Xs`;_ </k> <state> Rho:Map `.Map => X|->0` </state>
      when notBool `X in keys(Rho)`
  rule int .Ids; S => S  [structural]

// IMP+

  rule <k> halt; ~> _ => .K </k>

endmodule
