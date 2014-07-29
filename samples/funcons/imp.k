// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "funcons.k"

module IMP-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left]
                 > AExp "+" AExp              [left]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp
                 | "!" BExp
                 > BExp "&&" BExp             [left]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"               [bracket]
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"
                 | "if" "(" BExp ")"
                   Block "else" Block
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP
  imports IMP-SYNTAX
  imports FUNCONS
  rule X:Id => deref(boundValue(X))                                 [structural]
  rule E1 / E2  => intDivide(E1,E2)                                 [structural]
  rule E1 + E2  => intPlus(E1,E2)                                   [structural]
  rule E1 <= E2 => intLeq(E1,E2)                                    [structural]
  rule ! B => not(B)                                                [structural]
  rule B1 && B2 => ifTrue(B1,B2,false)                              [structural]
  rule {} => skip                                                   [structural]
  rule X:Id = E; => asgn(boundValue(X), E)                          [structural]
  rule if (B) S1 else S2 => ifTrue(B,S1,S2)                         [structural]
  rule while (B) S => whileTrue(B,S)                                [structural]
  rule S1 S2 => seq(S1,S2)                                          [structural]
  rule int .Ids ; S => S                                            [structural]
  rule int X:Id, Xs:Ids ; S  => scope(bind(X,alloc(0)), int Xs; S)  [structural]
endmodule
