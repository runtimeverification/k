// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 // remove division tag when we have proper search strategies
                 | "-" Int
                 | "(" AExp ")"               [bracket]
                 > AExp "/" AExp              [left, strict, group(division)]
                 > AExp "+" AExp              [left, strict]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, strict(1)]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "spawn" Stmt
                 > Stmt Stmt                  [left]

  syntax Ids   ::= List{Id,","}               [klabel(exps)]
  syntax AExps ::= List{AExp,","}             [klabel(exps)]
  syntax AExps ::= Ids
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Stmt </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I => 0 -Int I
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .
  rule {S} => S
// Stmt
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}

  rule <k> int (X,Xs => Xs); ...</k>
       <state> Rho (.Map => X |-> 0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; => .
endmodule
