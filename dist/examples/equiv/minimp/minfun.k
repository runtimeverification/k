module MINFUN-SYNTAX

syntax Exp ::= Id
	     | Exp "+" Exp [strict]
	     | Exp "-" Exp [strict]
	     | Exp "==" Exp [strict]
	     | Exp "<" Exp [strict]
	     | "if" Exp "then" Exp "else" Exp [strict(1)]
	     | Val
	     | "fix" Id Exp [binder]
	     > Exp Exp [seqstrict]
	     | "(" Exp ")" [bracket]

syntax Val ::= "lambda" Id "." Exp [binder]
             | Int
	     | Bool

endmodule

module MINFUN
  imports MINFUN-SYNTAX
  imports SUBSTITUTION

configuration <t> <k> $PGM:Exp </k> </t>

syntax KResult ::= Val

rule I1:Int + I2:Int => I1 +Int I2

rule I1:Int - I2:Int => I1 -Int I2

rule I1:Int == I2:Int => I1 ==Int I2

rule I1:Int < I2:Int => I1 <Int I2

rule if true then S1:Exp else _ => S1

rule if false then _ else S2:Exp => S2

rule (lambda X:Id . E:Exp) V:Val => E[V / X]

rule fix X:Id E:Exp => E[fix X E / X]

endmodule
