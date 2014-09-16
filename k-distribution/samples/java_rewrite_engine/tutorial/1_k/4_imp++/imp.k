// Copyright (c) 2013-2014 K Team. All Rights Reserved.


module IMP-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict]
                 > "spawn" Block
                 > Id "=" AExp                [strict(2)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"  [strict]
                 | "halt" ";"
                 > "join" AExp ";"            [strict]

  syntax Ids   ::= List{Id,","}               [strict]
  syntax AExps ::= List{AExp,","}             [strict]
  syntax Stmts ::= List{Stmt,""}
endmodule


module IMP
  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool | String

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <id color="black"> 0 </id>
                    </thread>
                  </threads>
                  <store color="red"> .Map </store>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> L:KItem ...</env>
       <store>... L |-> I:KItem ...</store>  [lookup,transition]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> L:KItem ...</env>
       <store>... L |-> (I => I +Int 1) ...</store>  [increment]
  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => .List ...</in>  [read]
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true  && B => B
  rule false && _ => false
// Block
  syntax KItem ::= env(Map)
  rule <k> { Ss } => Ss ~> env(Rho) ...</k>
       <env> Rho:Map </env>   [structural]
  rule <k> env(Rho:Map) => . ...</k> <env> _ => Rho </env>   [structural]
// Stmt
  rule _:Int; => .
  rule <k> X:Id = I:Int => I ...</k>
       <env>... X |-> L:KItem ...</env>
       <store>... L |-> (_:KItem => I) ...</store>  [assignment,transition]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) { S while(B) S } else { .Stmts }   [structural]

  rule <k> int (X:Id, Xs => Xs); ...</k>
       <env> Rho:Map => Rho[X <- !L:Int] </env>
       <store>... .Map => !L |-> 0 ...</store>
  [structural]
  rule int .Ids; => .   [structural]

  syntax AExp ::= Printable
  syntax Printable ::= Int | String
  rule <k> print(P:Printable, AEs => AEs); ...</k>
       <out>... .List => ListItem(P) </out>   [print]
  rule print(.AExps); => .  [structural]

  rule <k> halt; ~> _ => . </k>

  rule <k> spawn S => !T:Int ...</k> <env> Rho:Map </env>
       (. => <thread>... <k> S </k> <env> Rho </env> <id> !T </id> ...</thread>)
  rule <k> join(T:Int); => . ...</k>
       <thread>... <k> . </k> <id> T </id> ...</thread>

// Stmts
  rule .Stmts => .                  [structural]
  // the following has sort annotation to avoid ambiguity with Map, Set, etc
  rule S:Stmt Ss:Stmts => S ~> Ss   [structural]
endmodule

