// Copyright (c) 2014-2019 K Team. All Rights Reserved.

require "domains.k"
require "imp-syntax.k"

module IMP-B-CONFIG
  imports DOMAINS
  imports IMP-SYNTAX

  configuration <bT>
    <bk> .K /* $PGM:Pgm */ </bk>
    <bstate> .Map </bstate>
  </bT>

  syntax KResult ::= Int | Bool
endmodule

// TODO: auto-generate
module IMP-B-STRICT
  imports IMP-B-CONFIG

  rule <bk> HOLE / E2 => HOLE ~> #divi2(E2) ... </bk>     [tag(b), heat]
  rule <bk> HOLE ~> #divi2(E2) => HOLE / E2 ... </bk>     [tag(b), cool]
  rule <bk> I1:Int / HOLE => HOLE ~> #divi1(I1) ... </bk> [tag(b), heat]
  rule <bk> HOLE ~> #divi1(I1) => I1 / HOLE ... </bk>     [tag(b), cool]

  rule <bk> HOLE + E2 => HOLE ~> #addi2(E2) ... </bk>     [tag(b), heat]
  rule <bk> HOLE ~> #addi2(E2) => HOLE + E2 ... </bk>     [tag(b), cool]
  rule <bk> I1:Int + HOLE => HOLE ~> #addi1(I1) ... </bk> [tag(b), heat]
  rule <bk> HOLE ~> #addi1(I1) => I1 + HOLE ... </bk>     [tag(b), cool]

  rule <bk> HOLE <= E2 => HOLE ~> #lei2(E2) ... </bk>     [tag(b), heat]
  rule <bk> HOLE ~> #lei2(E2) => HOLE <= E2 ... </bk>     [tag(b), cool]
  rule <bk> I1:Int <= HOLE => HOLE ~> #lei1(I1) ... </bk> [tag(b), heat]
  rule <bk> HOLE ~> #lei1(I1) => I1 <= HOLE ... </bk>     [tag(b), cool]

  rule <bk> ! HOLE => HOLE ~> #noti() ... </bk>           [tag(b), heat]
  rule <bk> HOLE ~> #noti() => ! HOLE ... </bk>           [tag(b), cool]

  rule <bk> HOLE && E2 => HOLE ~> #andi(E2) ... </bk>     [tag(b), heat]
  rule <bk> HOLE ~> #andi(E2) => HOLE && E2 ... </bk>     [tag(b), cool]

  rule <bk> X = HOLE; => HOLE ~> #assigni(X) ... </bk>    [tag(b), heat]
  rule <bk> HOLE ~> #assigni(X) => X = HOLE; ... </bk>    [tag(b), cool]

  rule <bk> if(HOLE) S1 else S2 => HOLE ~> #ifi(S1,S2) ... </bk> [tag(b), heat]
  rule <bk> HOLE ~> #ifi(S1,S2) => if(HOLE) S1 else S2 ... </bk> [tag(b), cool]
endmodule

module IMP-B
  imports DOMAINS
  imports IMP-B-CONFIG
  imports IMP-B-STRICT

  // AExp
  rule <bk> X:Id => I ...</bk> <bstate>... X |-> I ...</bstate>    [tag(b)]
  rule <bk> I1 / I2 => I1 /Int I2 ... </bk> requires I2 =/=Int 0 [tag(b)]
  rule <bk> I1 + I2 => I1 +Int I2 ... </bk>                      [tag(b)]

  // BExp
  rule <bk> I1 <= I2 => I1 <=Int I2 ... </bk> [tag(b)]
  rule <bk> ! T => notBool T ... </bk>        [tag(b)]
  rule <bk> true && B => B ... </bk>          [tag(b)]
  rule <bk> false && _ => false ... </bk>     [tag(b)]

  // Block
  rule <bk> {} => .   ... </bk> [tag(b), structural]
  rule <bk> {S} => S  ... </bk> [tag(b), structural]

  // Stmt
  rule <bk> X = I:Int; => . ... </bk> <bstate>... X |-> (_ => I) ...</bstate> [tag(b)]
  rule <bk> S1:Stmt S2:Stmt => S1 ~> S2 ... </bk>                           [tag(b), structural]
  rule <bk> if (true)  S else _ => S ... </bk>                              [tag(b)]
  rule <bk> if (false) _ else S => S ... </bk>                              [tag(b)]
  rule <bk> while (B) S => if (B) {S while (B) S} else {} ... </bk>         [tag(b), structural]

  // Pgm
  rule <bk> int (X,Xs => Xs);_ </bk> <bstate> Rho:Map (.Map => X|->0) </bstate> requires notBool (X in keys(Rho)) [tag(b)]
  rule <bk> int .Ids; S => S ... </bk> [structural, tag(b)]
endmodule
