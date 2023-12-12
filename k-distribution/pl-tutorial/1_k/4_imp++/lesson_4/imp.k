// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
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
       <store>... N |-> I ...</store>  [group(lookup)]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [group(increment)]
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
  rule {} => .
  rule {S} => S
// Stmt
  rule <k> X = I:Int; => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}

  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => .

  syntax Printable ::= Int | String
/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable
  context print(HOLE:AExp, _);
  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <output>... .List => ListItem(P) </output>
  rule print(.AExps); => .
endmodule
