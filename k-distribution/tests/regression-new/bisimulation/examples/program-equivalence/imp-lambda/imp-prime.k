// Copyright (c) 2014-2019 K Team. All Rights Reserved.

require "domains.k"

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, klabel(divi)]
                 > AExp "+" AExp              [left, klabel(addi)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [klabel(lei)]
                 | "!" BExp                   [klabel(noti)]
                 > BExp "&&" BExp             [left, klabel(andi)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"                      [klabel(asigni)]
                 | "if" "(" BExp ")" Block "else" Block [klabel(ifi)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP-CONFIG
  imports DOMAINS
  imports IMP-SYNTAX

  configuration <impT>
    <impk> .K /* $PGM:Pgm */ </impk>
    <impstate> .Map </impstate>
  </impT>

  syntax KResult ::= Int | Bool
endmodule

// TODO: auto-generate
module IMP-STRICT
  imports IMP-CONFIG

  syntax KItem ::= #divi1(K) | #divi2(K)
  rule <impk> HOLE / E2 => HOLE ~> #divi2(E2) ... </impk>     [tag(a), heat]
  rule <impk> HOLE ~> #divi2(E2) => HOLE / E2 ... </impk>     [tag(a), cool]
  rule <impk> I1:Int / HOLE => HOLE ~> #divi1(I1) ... </impk> [tag(a), heat]
  rule <impk> HOLE ~> #divi1(I1) => I1 / HOLE ... </impk>     [tag(a), cool]

  syntax KItem ::= #addi1(K) | #addi2(K)
  rule <impk> HOLE + E2 => HOLE ~> #addi2(E2) ... </impk>     [tag(a), heat]
  rule <impk> HOLE ~> #addi2(E2) => HOLE + E2 ... </impk>     [tag(a), cool]
  rule <impk> I1:Int + HOLE => HOLE ~> #addi1(I1) ... </impk> [tag(a), heat]
  rule <impk> HOLE ~> #addi1(I1) => I1 + HOLE ... </impk>     [tag(a), cool]

  syntax KItem ::= #lei1(K) | #lei2(K)
  rule <impk> HOLE <= E2 => HOLE ~> #lei2(E2) ... </impk>     [tag(a), heat]
  rule <impk> HOLE ~> #lei2(E2) => HOLE <= E2 ... </impk>     [tag(a), cool]
  rule <impk> I1:Int <= HOLE => HOLE ~> #lei1(I1) ... </impk> [tag(a), heat]
  rule <impk> HOLE ~> #lei1(I1) => I1 <= HOLE ... </impk>     [tag(a), cool]

  syntax KItem ::= #noti()
  rule <impk> ! HOLE => HOLE ~> #noti() ... </impk>           [tag(a), heat]
  rule <impk> HOLE ~> #noti() => ! HOLE ... </impk>           [tag(a), cool]

  syntax KItem ::= #andi(K)
  rule <impk> HOLE && E2 => HOLE ~> #andi(E2) ... </impk>     [tag(a), heat]
  rule <impk> HOLE ~> #andi(E2) => HOLE && E2 ... </impk>     [tag(a), cool]

  syntax KItem ::= #assigni(K)
  rule <impk> X = HOLE; => HOLE ~> #assigni(X) ... </impk>    [tag(a), heat]
  rule <impk> HOLE ~> #assigni(X) => X = HOLE; ... </impk>    [tag(a), cool]

  syntax KItem ::= #ifi(K,K)
  rule <impk> if(HOLE) S1 else S2 => HOLE ~> #ifi(S1,S2) ... </impk> [tag(a), heat]
  rule <impk> HOLE ~> #ifi(S1,S2) => if(HOLE) S1 else S2 ... </impk> [tag(a), cool]
endmodule

module IMP
  imports DOMAINS
  imports IMP-CONFIG
  imports IMP-STRICT

  // AExp
  rule <impk> X:Id => I ...</impk> <impstate>... X |-> I ...</impstate>    [tag(a)]
  rule <impk> I1 / I2 => I1 /Int I2 ... </impk> requires I2 =/=Int 0 [tag(a)]
  rule <impk> I1 + I2 => I1 +Int I2 ... </impk>                      [tag(a)]

  // BExp
  rule <impk> I1 <= I2 => I1 <=Int I2 ... </impk> [tag(a)]
  rule <impk> ! T => notBool T ... </impk>        [tag(a)]
  rule <impk> true && B => B ... </impk>          [tag(a)]
  rule <impk> false && _ => false ... </impk>     [tag(a)]

  // Block
  rule <impk> {} => .   ... </impk> [tag(a), structural]
  rule <impk> {S} => S  ... </impk> [tag(a), structural]

  // Stmt
  rule <impk> X = I:Int; => . ... </impk> <impstate>... X |-> (_ => I) ...</impstate> [tag(a)]
  rule <impk> S1:Stmt S2:Stmt => S1 ~> S2 ... </impk>                           [tag(a), structural]
  rule <impk> if (true)  S else _ => S ... </impk>                              [tag(a)]
  rule <impk> if (false) _ else S => S ... </impk>                              [tag(a)]
  rule <impk> while (B) S => if (B) {S while (B) S} else {} ... </impk>         [tag(a), structural]

  // Pgm
  rule <impk> int (X,Xs => Xs);_ </impk> <impstate> Rho:Map (.Map => X|->0) </impstate> requires notBool (X in keys(Rho)) [tag(a)]
  rule <impk> int .Ids; S => S ... </impk> [structural, tag(a)]
endmodule
