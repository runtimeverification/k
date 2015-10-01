// Copyright (c) 2014-2015 K Team. All Rights Reserved.
requires "domains.k"

module IMP-CORE-SYNTAX
  imports EMPTY-ID
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left]
                 > AExp "+" AExp              [left]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [latex({#1}\leq{#2})]
                 | "!" BExp
                 > BExp "&&" BExp             [left]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"
                 | "if" "(" BExp ")"
                   Block "else" Block
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP-SYNTAX
  imports ID
  imports IMP-CORE-SYNTAX
endmodule

module IMP
  imports IMP-CORE-SYNTAX
  imports MAP
  imports INT
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm:K </k>
                  <state color="red"> .Map </state>
                </T>

//// AExp
//  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
//  rule I1:Int + I2:Int => I1 +Int I2
//// BExp
//  rule I1:Int <= I2:Int => I1 <=Int I2
//  rule ! T:Bool => notBool T
//  rule true && B => B
//  rule false && _ => false
//// Block
//  rule {} => .K   [structural]
//  rule {S} => S  [structural]
//// Stmt
//  rule <k> X = I:Int; => .K ...</k> <state>... X |-> `_ => I` ...</state>
//  rule S1::Stmt S2::Stmt => S1 ~> S2  [structural]
//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
//  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int `X,Xs => Xs`;_ </k> <state> Rho:Map `.Map => X|->0` </state>
    when notBool `X in keys(Rho)`
  rule int .Ids; S => S  [structural]

  //rule K ~> .K => K     [anywhere]
  //rule .K ~> K => K     [anywhere]
endmodule

//rule
//<T>(
//    <k>(OR(
//        AND(int_;_(=>(_,_(X,Xs),Xs),_12),isRule(#token("-569738558",Int))),
//        AND(
//            =>(
//                #KSequence(int_;_(.List{"'_,_"}(),S),DotVar1),
//                AND(#KSequence(S,DotVar1),isRule(#token("1747612906",Int)))),
//            OR(isRule(#token("1747612906",Int)))))),
//    OR(AND(<state>(=>(_0,_Map_(Rho,_|->_(X,#token("0",Int))))),isRule(#token("-569738558",Int))),AND(DotVar0,isRule(#token("1747612906",Int))))) requires #token("true",Bool) ensures #token("true",Bool) [automaton()]

// rule <T>(<k>(OR(AND(int_;_(=>(_,_(X,Xs),AND(Xs,isRule(#token("-569738558",Int)))),_12),OR(isRule(#token("-569738558",Int)))),AND(=>(#KSequence(int_;_(.List{"'_,_"}(),S),DotVar1),AND(#KSequence(S,DotVar1),isRule(#token("1747612906",Int)))),OR(isRule(#token("1747612906",Int)))))),OR(AND(<state>(=>(_0,AND(_Map_(Rho,_|->_(X,#token("0",Int))),isRule(#token("-569738558",Int))))),OR(isRule(#token("-569738558",Int)))),AND(DotVar0,isRule(#token("1747612906",Int))))) requires #token("true",Bool) ensures #token("true",Bool) [automaton()]
