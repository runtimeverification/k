// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module MINFUN-SYNTAX

syntax FExp ::= Id
         | FExp "f+" FExp [strict]
         | FExp "f-" FExp [strict]
         | FExp "f==" FExp [strict]
         | FExp "f<" FExp [strict]
         | "fif" FExp "fthen" FExp "felse" FExp [strict(1)]
         | Val
         | "let" Id "be" FExp "in" FExp [strict(2), binder]
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

rule fif true fthen S1:FExp felse _ => S1

rule fif false fthen _ felse S2:FExp => S2

rule (lambda X:Id . E:FExp) V:Val => E[V / X]

rule let X:Id be V:Val in E:FExp => E[V / X]

rule fix X:Id E:FExp => E[fix X E / X]

endmodule
