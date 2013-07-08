require "builtins/map.k"

module IMP-SYNTAX
  //syntax AExp  ::= Int | String | Id
  syntax AExp  ::= Int | Id
                 | "++" Id
                 //| "read" "(" ")"
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
                 //| "print" "(" AExps ")" ";"  [strict]
                 | "halt" ";"
                 > "join" AExp ";"            [strict]

  syntax Ids   ::= List{Id,","}               [strict]
  //syntax AExps ::= List{AExp,","}             [strict]
  syntax Stmts ::= List{Stmt,""}
endmodule


module IMP
  imports IMP-SYNTAX
  imports MAP
  //syntax KResult ::= Int | Bool | String
  syntax KResult ::= Int | Bool

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
                  //<in color="magenta" stream="stdin"> .List </in>
                  //<out color="Orchid" stream="stdout"> .List </out>
                </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N:KItem ...</env>
       <store>... N |-> I:KItem ...</store>  [lookup]
  rule <k> ++X:Id => I +Int 1 ...</k>
       <env>... X |-> N:KItem ...</env>
       <store>... N |-> (I:KItem => I +Int 1) ...</store>  [increment]
  //rule <k> read() => I ...</k>
  //     <in> ListItem(I:Int) => . ...</in>  [read]
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
  //rule Str1:String + Str2:String => Str1 +String Str2
// BExp
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule ! T:Bool => notBool T
  rule true && B:KItem => B
  rule false && _:KItem => false
// Block
  rule <k> {Ss:KItem} => Ss ~> Rho ...</k>
       <env> Rho:MyMap </env>  [structural]
  rule <k> Rho:MyMap => . ...</k> <env> _:MyMap => Rho </env>  [structural]
// Stmt
  rule _:Int; => .
  rule <k> X:Id = I:Int => I ...</k>
       <env>... X |-> N:KItem ...</env>
       <store>... N |-> (_:KItem => I) ...</store>  [assignment]
  rule if (true)  S:KItem else _:KItem => S
  rule if (false) _:KItem else S:KItem => S
  rule while (B:KItem) S:KItem => if (B) {S while (B) S} else {.Stmts}
    [structural]

  rule <k> int (X:Id,Xs:Ids => Xs); ...</k>
       <env> Rho:MyMap => Rho[X <- N] </env>
       <store>... .MyMap => N |-> 0 ...</store>
    when fresh(N:Int)
    [structural]
  rule int .Ids; => .  [structural]

  //syntax AExp ::= Printable
  //syntax Printable ::= Int | String
  //rule <k> print(P:Printable,AEs => AEs); ...</k>
  //     <out>... . => ListItem(P) </out>  [print]
  //rule print(.AExps); => .  [structural]
  
  rule <k> halt; ~> _ => . </k>

  rule <k> spawn S:KItem => T ...</k>
       <env> Rho:MyMap </env>
       (. => <thread>... <k> S </k> <env> Rho </env> <id> T </id> ...</thread>)
    when fresh(T:Int)
  rule <k> join(T:KItem); => . ...</k>
       <thread>...
         <k> . </k>
         <id> T </id>
       ...</thread>

// Stmts
  rule .Stmts => .
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]
endmodule
