// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module MINIMP-SYNTAX

syntax Exp ::= Id
                | Int
         | Bool
         | Exp "i+" Exp [strict]
         | Exp "i-" Exp [strict]
         | Exp "i==" Exp [strict]
         | Exp "i<" Exp [strict]

syntax Stmt ::= Id ":=" Exp [strict(2)]
              | "skip"
          | Stmt ";" Stmt [left]
          | "if" Exp "then" Stmt "else" Stmt [strict(1)]
          | "while" Exp "do" Stmt
          | "{" Stmt "}" [bracket]

syntax Code ::= Exp | Stmt

endmodule

module MINIMP
  imports MINIMP-SYNTAX

configuration <t> <k> $PGM:K </k> <env> .Map </env> </t>

syntax KResult ::= Int | Bool

rule <k> I:Id => I1:Int ...</k> <env>... I |-> I1 ...</env>

rule I1:Int i+ I2:Int => I1 +Int I2

rule I1:Int i- I2:Int => I1 -Int I2

rule I1:Int i== I2:Int => I1 ==Int I2

rule I1:Int i< I2:Int => I1 <Int I2

rule <k> I:Id := I1:Int => . ...</k> <env>... I |-> (_ => I1) ...</env>

rule <k> I:Id := I1:Int => . ...</k> <env> Rho:Map (. => I |-> I1) </env> when notBool(I in keys(Rho))

rule S1:Stmt ; S2:Stmt => S1 ~> S2

rule if true then S1:Stmt else _ => S1

rule if false then _ else S2:Stmt => S2

rule while E:Exp do S:Stmt => if E then (S; while E do S) else skip

endmodule
