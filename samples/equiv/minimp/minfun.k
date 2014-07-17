// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module MINFUN-SYNTAX

syntax FExp ::= Id
         | FExp "f+" FExp [strict]
         | FExp "f-" FExp [strict]
         | FExp "f==" FExp [strict]
         | FExp "f<" FExp [strict]
         | "if" FExp "then" FExp "else" FExp [strict(1)]
         | Val
         | "fix" Id FExp [binder]
         > FExp FExp [seqstrict]
         | "(" FExp ")" [bracket]

syntax Val ::= "lambda" Id "." FExp [binder]
             | Int
         | Bool

endmodule

module MINFUN
  imports MINFUN-SYNTAX
  imports SUBSTITUTION

configuration <t> <k> $PGM:K </k> </t>

syntax KResult ::= Val

rule I1:Int f+ I2:Int => I1 +Int I2

rule I1:Int f- I2:Int => I1 -Int I2

rule I1:Int f== I2:Int => I1 ==Int I2

rule I1:Int f< I2:Int => I1 <Int I2

rule if true then S1:FExp else _ => S1

rule if false then _ else S2:FExp => S2

rule (lambda X:Id . E:FExp) V:Val => E[V / X]

rule fix X:Id E:FExp => E[fix X E / X]

endmodule
