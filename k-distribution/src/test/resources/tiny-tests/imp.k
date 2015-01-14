// Copyright (c) 2010-2014 K Team. All Rights Reserved.

module INT
  syntax Int ::= Token{[\-\+]? [0-9]+} [regex("[\\+-]?\\d+"), prefer]
endmodule

module ID
  syntax Id ::= Token{[A-Za-z\_][A-Za-z0-9\_]*}   [notInRules, regex("(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*")]
endmodule

module BOOL
  syntax Bool ::= "true" | "false"
endmodule

module IMP-SYNTAX
  imports INT 
  imports ID
  imports BOOL

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
endmodule

module IMP
  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>

  rule `_/_`(I1,I2) => `_/Int_`(I1,I2) when `_=/=Int_`(I2, 0)
  rule `_+_`(I1,I2) => `_+Int_`(I1,I2)

  rule `_<=_`(I1,I2) => `_<=Int_`(I1, I2)
  rule `!`(T) => notBool(T)
  rule `_&&_`(#token("Boolean","true"),B) => B
  rule `_&&_`(#token("Boolean","false"),_) => #token("Boolean","false")

  rule {} => .   [structural]
  rule {S} => S  [structural]

  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>

  rule `__`(S1,S2) => S1 ~> S2 when and(isStmt(S1),isStmt(S2))  [structural]

//  rule `if(_)_else_`(#token("Boolean","true"),S,_) => S
  rule if (false) _ else S => S

  rule while (B) S => if (B) {S while (B) S} else {}  [structural]

  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]
endmodule
