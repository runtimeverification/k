// Copyright (c) 2014-2019 K Team. All Rights Reserved.

require "domains.k"
require "imp-syntax.k"

module IMP-A-CONFIG
  imports DOMAINS
  imports IMP-SYNTAX

  configuration <aT>
    <ak> .K /* $PGM:Pgm */ </ak>
    <astate> .Map </astate>
  </aT>

  syntax KResult ::= Int | Bool
endmodule

// TODO: auto-generate
module IMP-A-STRICT
  imports IMP-A-CONFIG

  rule <ak> HOLE / E2 => HOLE ~> #divi2(E2) ... </ak>     [tag(a), heat]
  rule <ak> HOLE ~> #divi2(E2) => HOLE / E2 ... </ak>     [tag(a), cool]
  rule <ak> I1:Int / HOLE => HOLE ~> #divi1(I1) ... </ak> [tag(a), heat]
  rule <ak> HOLE ~> #divi1(I1) => I1 / HOLE ... </ak>     [tag(a), cool]

  rule <ak> HOLE + E2 => HOLE ~> #addi2(E2) ... </ak>     [tag(a), heat]
  rule <ak> HOLE ~> #addi2(E2) => HOLE + E2 ... </ak>     [tag(a), cool]
  rule <ak> I1:Int + HOLE => HOLE ~> #addi1(I1) ... </ak> [tag(a), heat]
  rule <ak> HOLE ~> #addi1(I1) => I1 + HOLE ... </ak>     [tag(a), cool]

  rule <ak> HOLE <= E2 => HOLE ~> #lei2(E2) ... </ak>     [tag(a), heat]
  rule <ak> HOLE ~> #lei2(E2) => HOLE <= E2 ... </ak>     [tag(a), cool]
  rule <ak> I1:Int <= HOLE => HOLE ~> #lei1(I1) ... </ak> [tag(a), heat]
  rule <ak> HOLE ~> #lei1(I1) => I1 <= HOLE ... </ak>     [tag(a), cool]

  rule <ak> ! HOLE => HOLE ~> #noti() ... </ak>           [tag(a), heat]
  rule <ak> HOLE ~> #noti() => ! HOLE ... </ak>           [tag(a), cool]

  rule <ak> HOLE && E2 => HOLE ~> #andi(E2) ... </ak>     [tag(a), heat]
  rule <ak> HOLE ~> #andi(E2) => HOLE && E2 ... </ak>     [tag(a), cool]

  rule <ak> X = HOLE; => HOLE ~> #assigni(X) ... </ak>    [tag(a), heat]
  rule <ak> HOLE ~> #assigni(X) => X = HOLE; ... </ak>    [tag(a), cool]

  rule <ak> if(HOLE) S1 else S2 => HOLE ~> #ifi(S1,S2) ... </ak> [tag(a), heat]
  rule <ak> HOLE ~> #ifi(S1,S2) => if(HOLE) S1 else S2 ... </ak> [tag(a), cool]
endmodule

module IMP-A
  imports DOMAINS
  imports IMP-A-CONFIG
  imports IMP-A-STRICT

  // AExp
  rule <ak> X:Id => I ...</ak> <astate>... X |-> I ...</astate>    [tag(a)]
  rule <ak> I1 / I2 => I1 /Int I2 ... </ak> requires I2 =/=Int 0 [tag(a)]
  rule <ak> I1 + I2 => I1 +Int I2 ... </ak>                      [tag(a)]

  // BExp
  rule <ak> I1 <= I2 => I1 <=Int I2 ... </ak> [tag(a)]
  rule <ak> ! T => notBool T ... </ak>        [tag(a)]
  rule <ak> true && B => B ... </ak>          [tag(a)]
  rule <ak> false && _ => false ... </ak>     [tag(a)]

  // Block
  rule <ak> {} => .   ... </ak> [tag(a), structural]
  rule <ak> {S} => S  ... </ak> [tag(a), structural]

  // Stmt
  rule <ak> X = I:Int; => . ... </ak> <astate>... X |-> (_ => I) ...</astate> [tag(a)]
  rule <ak> S1:Stmt S2:Stmt => S1 ~> S2 ... </ak>                           [tag(a), structural]
  rule <ak> if (true)  S else _ => S ... </ak>                              [tag(a)]
  rule <ak> if (false) _ else S => S ... </ak>                              [tag(a)]
  rule <ak> while (B) S => if (B) {S while (B) S} else {} ... </ak>         [tag(a), structural]

  // Pgm
  rule <ak> int (X,Xs => Xs);_ </ak> <astate> Rho:Map (.Map => X|->0) </astate> requires notBool (X in keys(Rho)) [tag(a)]
  rule <ak> int .Ids; S => S ... </ak> [structural, tag(a)]
endmodule
