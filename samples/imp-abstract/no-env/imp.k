// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/model-checker.k"

/*@
This is the abstract semantics of IMP. It contains the normal semantics of IMP
and its extension for abstact execution.
*/

module ABSTRACT-DOMAIN-SYNTAX
  syntax Int ::= "anyInt"
  syntax Bool ::= "anyBool"
endmodule

module IMP-SYNTAX
  imports ABSTRACT-DOMAIN-SYNTAX


  syntax AExp  ::= Int | Id
                 | AExp "*" AExp              [left, strict]
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 > Id "=" AExp                [strict(2)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | AExp "==" AExp             [seqstrict]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "spawn" "{" Process "}"

  syntax Process ::=  "int" Ids ";" Stmts
  syntax Pgm ::= "main" "{" Process "}" | LTLFormula

  syntax Ids   ::= List{Id,","}
  syntax Stmts   ::= List{Stmt,""}
endmodule


module ABSTRACT-DOMAIN
  imports ABSTRACT-DOMAIN-SYNTAX
  syntax Bool ::= K "generalizes" K [function]
  rule B:Bool generalizes B => true
  rule I:Int generalizes I => true
  rule anyBool generalizes _:Bool => true
  rule anyInt generalizes I:Int => true

  syntax Int ::= Int "plusInt" Int [function]
  syntax Int ::= Int "timesInt" Int [function]

  rule anyInt timesInt _:Int => anyInt
  rule _:Int timesInt anyInt => anyInt

  rule I1:Int timesInt I2:Int => #if I1 *Int I2 <=Int 2 ==K true #then  I1 *Int I2 #else anyInt #fi

  rule anyInt plusInt _:Int => anyInt
  rule _:Int plusInt anyInt => anyInt

  rule I1:Int plusInt I2:Int => #if I1 +Int I2 <=Int 2 ==K true #then  I1 +Int I2 #else anyInt #fi

  rule anyInt divInt I:Int => anyInt  when I =/=Int 0
  rule _:Int divInt anyInt => anyInt

  rule anyInt <=Int _:Int => anyBool
  rule _:Int <=Int anyInt => anyBool

  rule anyInt ==Int _:Int => anyBool
  rule _:Int ==Int anyInt => anyBool

  rule anyInt =/=Int _:Int => anyBool
  rule _:Int =/=Int anyInt => anyBool

  rule anyBool ==Bool _:Bool => anyBool
  rule _:Bool ==Bool anyBool => anyBool

  rule false andBool B:Bool => false
  rule B:Bool andBool false => false

  rule anyBool andBool B:Bool => anyBool  when B =/=Bool false
//  rule B:Bool andBool anyBool) => anyBool  when B =/=Bool false
  rule '_andBool_(B:Bool,, anyBool) => anyBool  when B =/=Bool false

  rule true orBool B:Bool => true
  rule B:Bool orBool true => true

  rule anyBool orBool B:Bool => anyBool  when B =/=Bool true
  rule '_orBool_(B:Bool,, anyBool) => anyBool  when B =/=Bool true

  rule notBool anyBool => anyBool
endmodule


module IMP-PREDICATES
  imports LTL-HOOKS
  imports MODEL-CHECKER-HOOKS

  syntax Val ::= Int | Bool


  syntax Prop ::= "eqTo" "(" Id "," Val ")"
               |  "lt" "(" Id "," Val ")"
               |  "leq" "(" Id "," Val ")"
               |  "gt" "(" Id "," Val ")"
               |  "geq" "(" Id "," Val ")"
               |  "neqTo" "(" Id "," Val ")"




 syntax Int ::= "val" "(" Bag "," Id ")" [function]


  configuration <T> <store> .Map </store> </T>

  rule val(<generatedTop><T>...
                 <store>... X |-> I:Int ...</store>
           ...</T> </generatedTop>, X)
       =>
       I
/*
  rule val(<T>...
                 <store>... X |-> I:Int ...</store>
           ...</T>, X)
       =>
       I
*/

  rule B:Bag |=Ltl eqTo(X:Id, I:Int) => true when val(B, X) ==K I [anywhere]

  rule B:Bag |=Ltl neqTo(X:Id, I:Int) => true when val(B, X) =/=K I [anywhere]

  rule B:Bag |=Ltl lt(X:Id, I:Int) => true when val(B, X) <Int I [anywhere]

  rule B:Bag |=Ltl leq(X:Id, I:Int) => true when val(B, X) <=Int I [anywhere]

  rule B:Bag |=Ltl gt(X:Id, I:Int) => true when val(B, X) >Int I [anywhere]

  rule B:Bag |=Ltl geq(X:Id, I:Int) => true when val(B, X) >=Int I [anywhere]
endmodule

module IMP
  imports IMP-SYNTAX
  imports IMP-PREDICATES
  imports ABSTRACT-DOMAIN

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Pgm </k>
                      <env color="LightSkyBlue"> .Map </env>
//                      <id color="black"> 0 </id>
                    </thread>
                  </threads>
                  <store color="red"> .Map </store>
//                  <in color="magenta" stream="stdin"> .List </in>
//                  <out color="Orchid" stream="stdout"> .List </out>
                </T>

/*@ The concrete semantics of IMP which remains unchanged for symbolic execution */
// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> I ...</env>  [local]
  rule <k> X:Id => I ...</k>
       <env> Rho </env>
       <store>... X |-> I ...</store>
    when notBool(X in keys(Rho))
    [transition]
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 plusInt I2
  rule I1:Int * I2:Int => I1 timesInt I2
// BExp
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int == I2:Int => I1 ==Int I2
  rule ! T:Bool => notBool T
//  rule true && B => B
//  rule false && _ => false
// Block
  rule <k> {Ss} => Ss  ...</k>  [structural]
// Stmt
  rule _:Int; => .
  rule <k> X = I:Int => I ...</k>
       <env>... X |-> (_ => I) ...</env>  [local]

  rule <k> X = I:Int => I ...</k>
       <env> Rho </env>
       <store>... X |-> (_ => I) ...</store>
    when notBool(X in keys(Rho)) [transition]

//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {.Stmts}  [structural]

  rule <k> spawn { P } => . ...</k>
       (. => <thread>... <k> P </k>  ...</thread>)


// Stmts
  rule <k> _ ~> (.Stmts => .) ...</k>
  rule S Ss => S ~> Ss  [structural]

//@ IMP symbolic semantics
  rule I1:Int / I2:Int => I1 divInt I2
    when I2 =/=Int 0
  rule I1:Int / I2:Int => I1 divInt I2
       when (I2 =/=Int 0) generalizes true [transition]

  rule true && B2:BExp => B2
  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       when (B1 ==Bool true) generalizes true  [transition]

  rule false && B2:BExp => false
  rule <k> B1:Bool && B2:BExp => false ...</k>
       when (B1 ==Bool false) generalizes true  [transition]

  rule if (true) S:Block else _ => S
  rule <k> if (B:Bool) S:Block else _ => S ...</k>
       when (B ==Bool true) generalizes true  [transition]

  rule if (false) _ else S:Block => S
  rule <k> if (B:Bool) _ else S:Block => S ...</k>
       when (B ==Bool false) generalizes true  [transition]


  rule <k> main { int (X:Id,Xs => Xs); S } ...</k>
       <store>... . => X |-> 0 ...</store>
  rule main { int .Ids; S } => S  [structural]

  rule <k> int (X:Id,Xs => Xs); S ...</k>
       <env>... . => X |-> 0 ...</env>
  rule int .Ids; S => S  [structural]

 endmodule
