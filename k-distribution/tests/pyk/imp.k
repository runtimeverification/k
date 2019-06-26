// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module IMP-SYNTAX
  imports BOOL-SYNTAX
  imports INT-SYNTAX
  imports ID

  syntax AExp  ::= Int | Id
                 | "-" Int                    [klabae(-_), symbol, format(%1%2)]
                 | AExp "/" AExp              [klabel(_/_), symbol, left, strict, color(pink)]
                 > AExp "+" AExp              [klabel(_+_), symbol, left, strict, color(pink)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [klabel(_<=_), symbol, seqstrict, latex({#1}\leq{#2}), color(pink)]
                 | "!" BExp                   [klabel(!_), symbol, strict, color(pink)]
                 > BExp "&&" BExp             [klabel(_&&_), symbol, left, strict(1), color(pink)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"                    [klabel({}), symbol]
                 | "{" Stmt "}"               [klabel({_}), symbol, format(%1%i%n%2%d%n%3)]
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [klabel(_=_;), symbol, strict(2), color(pink), format(%1 %2 %3%4)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [klabel(if(_)_else_), symbol, strict(1), colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7)]
                 | "while" "(" BExp ")" Block [klabel(while(_)_), symbol, colors(yellow,white,white), format(%1 %2%3%4 %5)]
                 > Stmt Stmt                  [klabel(__), symbol, left, format(%1%n%2)]

  syntax Pgm ::= "int" Ids ";" Stmt           [klabel(int_;_), symbol, format(%1 %2%3%n%4), colors(yellow,pink)]
  syntax Ids ::= List{Id,","}                 [klabel(_,_), symbol, format(%1%2 %3)]
endmodule

module IMP
  imports IMP-SYNTAX
  imports BOOL
  imports INT
  imports MAP

  syntax KResult ::= Int | Bool
  syntax KItem   ::= Pgm

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>

  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I1 => 0 -Int I1

  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false

  rule {} => .   [structural]
  rule {S} => S  [structural]

  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>

  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]

  rule if (true)  S else _ => S
  rule if (false) _ else S => S

  rule while (B) S => if (B) {S while (B) S} else {}  [structural]

  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]
endmodule
