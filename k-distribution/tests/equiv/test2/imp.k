// Copyright (c) 2016-2019 K Team. All Rights Reserved.

require "domains.k"

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
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
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule

module CFG
imports DOMAINS
imports IMP-SYNTAX
configuration
<T>
<L1 color="yellow">
  <k color="green"> $PGM:Stmt </k>
  <state color="red"> .Map </state>
</L1>
<L2 color="yellow">
  <k color="green"> $PGM:Stmt </k>
  <state color="red"> .Map </state>
</L2>
</T>
endmodule

module IMP
imports CFG
endmodule
