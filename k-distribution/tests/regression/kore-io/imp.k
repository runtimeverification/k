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
                 | "while" "(" BExp ")" Block
                 | "print" "(" AExp ")" ";"   [strict]
                 | "halt" ";"
                 > Stmt Stmt                  [left]

  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP-SYNTAX
  imports ID
  imports IMP-COMMON
endmodule

module IMP
  imports INT
  imports BOOL
  imports STRING
  imports K
  imports LIST
  imports MAP
  imports SET
  imports STDIN-STREAM
  imports STDOUT-STREAM
  imports IMP-COMMON

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> `$PGM:Pgm`:K </k>
                  <state color="red"> .Map </state>
                  <stdin/>
                  <stdout/>
                </T>

// AExp

  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>

  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2

// BExp

  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
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

  rule while (B) S => if (B) {S while (B) S} else {}  [structural]

// Pgm

  rule <k> int `X,Xs => Xs`;_ </k> <state> Rho:Map `.Map => X|->0` </state>
      when notBool `X in keys(Rho)`
  rule int .Ids; S => S  [structural]

// IMP+

  syntax KResult ::= String
  rule Str1 + Str2 => Str1 +String Str2

  rule <k> halt; ~> _ => .K </k>

// IO

  rule <k> read() => I ...</k>
       <stdin> ListItem(I:Int) => .List ...</stdin>
       when isStream(I) =/=K true
       [read]

  // TODO(daejunpark): need to be implicitly done by kompile?
  rule <k> read() ... </k>
       <stdin>
         `.List => ListItem(#parseInput("Int", " \n\t\r"))`
         ListItem(#buffer(_:String))
         ...
       </stdin>

  syntax Printable ::= Int | String
  syntax AExp ::= Printable
  rule <k> print(P:Printable); => .K ...</k>
       <stdout>... .List => ListItem(P) </stdout>  [print]

endmodule
