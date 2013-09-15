require "builtins/list.k"
require "builtins/map.k"
require "io/io.k"


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
  imports LIST
  imports MAP
  imports IO

  syntax KResult ::= Int | Bool | String

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Stmts </k>
                      //<k color="green"> $PGM:K </k>
                      <env color="LightSkyBlue"> .MyMap </env>
                      <id color="black"> 0 </id>
                    </thread>
                  </threads>
                  <store color="red"> .MyMap </store>
                  <in color="magenta" stream="stdin"> .MyList </in>
                  <out color="Orchid" stream="stdout"> .MyList </out>
                </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> L:KItem ...</env>
       <store>... L |-> I:KItem ...</store>  [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> L:KItem ...</env>
       <store>... L |-> (I => I +Int 1) ...</store>  [increment]
  rule <k> read() => I ...</k>
       <in> MyListItem(I:Int) => .MyList ...</in>  [read]
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true  && B => B
  rule false && _ => false
// Block
  rule <k> { Ss } => Ss ~> Rho ...</k>
       <env> Rho:MyMap </env>   [structural]
  rule <k> Rho:MyMap => . ...</k> <env> _ => Rho </env>   [structural]
// Stmt
  rule _:Int; => .
  rule <k> X:Id = I:Int => I ...</k>
       <env>... X |-> L:KItem ...</env>
       <store>... L |-> (_:KItem => I) ...</store>  [assignment]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) { S while(B) S } else { .Stmts }   [structural]

  rule <k> int (X:Id, Xs => Xs); ...</k>
       <env> Rho:MyMap => Rho[X <- L] </env>
       <store>... .MyMap => L |-> 0 ...</store>
    when fresh(L:Int)   [structural]
  rule int .Ids; => .   [structural]

  syntax AExp ::= Printable
  syntax Printable ::= Int | String
  rule <k> print(P:Printable, AEs => AEs); ...</k>
       <out>... .MyList => MyListItem(P) </out>   [print]
  rule print(.AExps); => .  [structural]
  
  rule <k> halt; ~> _ => . </k>

  rule <k> spawn S => T ...</k> <env> Rho:MyMap </env>
       (. => <thread>... <k> S </k> <env> Rho </env> <id> T </id> ...</thread>)
    when fresh(T:Int)
  rule <k> join(T:Int); => . ...</k>
       <thread>... <k> . </k> <id> T </id> ...</thread>

// Stmts
  rule .Stmts => .                  [structural]
  // the following has sort annotation to avoid ambiguity with MyMap, MySet, etc
  rule S:Stmt Ss:Stmts => S ~> Ss   [structural]
endmodule

