// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "modules/k-functional-visitor.k"

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
                 | "{" Stmt "}"
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
  imports K-FUNCTIONAL-VISITOR

  configuration <k> test($PGM:Pgm) </k>

  syntax KItem ::= test(K)
  rule test(KI:KItem) => #visit(KI, '_+Int_, 1, isInt, .KList)
endmodule

