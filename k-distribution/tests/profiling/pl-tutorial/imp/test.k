// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module IMP-SYNTAX
  imports public DOMAINS-SYNTAX
  syntax AExp  ::=
    Int
  | Id
  | "-" Int [format(%1%2)]
  | AExp "/" AExp [color(pink), left, strict]
  | "(" AExp ")" [bracket]
  > AExp "+" AExp [color(pink), left, strict]
  syntax BExp  ::=
    Bool
  | AExp "<=" AExp [color(pink), latex({#1}\leq{#2}), seqstrict]
  | "!" BExp [color(pink), strict]
  | "(" BExp ")" [bracket]
  > BExp "&&" BExp [color(pink), left, strict(1)]
  syntax Block  ::=
    "{" "}"
  | "{" Stmt "}" [format(%1%i%n%2%d%n%3)]
  syntax Stmt  ::=
    Block
  | Id "=" AExp ";" [color(pink), format(%1 %2 %3%4), strict(2)]
  | "if" "(" BExp ")" Block "else" Block [colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7), strict(1)]
  | "while" "(" BExp ")" Block [colors(yellow,white,white), format(%1 %2%3%4 %5)]
  > Stmt Stmt [format(%1%n%2), left]
  syntax Pgm  ::=
    "int" Ids ";" Stmt [colors(yellow,pink), format(%1 %2%3%n%4)]
  syntax Ids  ::=
    List{Id,","} [format(%1%2 %3)]
endmodule

module IMP
  imports public IMP-SYNTAX
  imports public DOMAINS
  syntax KResult  ::=
    Int
  | Bool
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
  rule {} => .
  rule {S} => S
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S
endmodule
