// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 | "-" Int
                 > AExp "/" AExp              [left, strict, division]
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
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "spawn" Stmt
                 > Stmt Stmt                  [left]

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax AExps ::= Ids
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int | Bool | String

  configuration <T color="yellow">
                  <k color="green"> $PGM:Stmt </k>
                  <env color="LightSkyBlue"> .Map </env>
                  <store color="red"> .Map </store>
                  <input color="magenta" stream="stdin"> .List </input>
                  <output color="Orchid" stream="stdout"> .List </output>
                </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [increment]
  rule <k> read() => I ...</k>
       <input> ListItem(I:Int) => .List ...</input>
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I => 0 -Int I
  rule Str1 + Str2 => Str1 +String Str2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule <k> {S} => S ~> Rho ...</k> <env> Rho </env>  [structural]
  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]

  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => .  [structural]

  syntax Printable ::= Int | String
/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable
  context print(HOLE:AExp, AEs:AExps);
  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <output>... .List => ListItem(P) </output>
  rule print(.AExps); => .  [structural]

  rule <k> halt; ~> _ => . </k>
endmodule
