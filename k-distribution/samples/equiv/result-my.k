// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module RESULT
imports SUBSTITUTION

syntax FExp ::= Id
              | FExp "f+" FExp [strict, klabel('_f+_)]
              | FExp "f-" FExp [strict, klabel('_f-_)]
              | FExp "f==" FExp [strict, klabel('_f==_)]
              | FExp "f<" FExp [strict, klabel('_f<_)]
              | "if" FExp "then" FExp "else" FExp [strict(1), klabel
              ('if_then_else_)]
              | Val
              | "fix" Id FExp [binder, klabel('fix__)]
              > FExp FExp [seqstrict, klabel('__)]
              | "(" FExp ")" [bracket, klabel('(_))]

syntax Val ::= "lambda" Id "." FExp [binder, klabel('lambda_._)]
             | Int
             | Bool

syntax KResult ::= Val

rule I1:Int f+ I2:Int => I1 +Int I2

rule I1:Int f- I2:Int => I1 -Int I2

rule I1:Int f== I2:Int => I1 ==Int I2

rule I1:Int f< I2:Int => I1 <Int I2

rule if true then S1:FExp else _:K => S1

rule if false then _:K else S2:FExp => S2

rule (lambda X:Id . E:FExp) V:Val => E [ V / X ]

rule fix X:Id E:FExp => E [ (fix X E) / X ]

syntax Exp ::= Id
             | Int
             | Bool
             | Exp "i+" Exp [strict, klabel('_i+_)]
             | Exp "i-" Exp [strict, klabel('_i-_)]
             | Exp "i==" Exp [strict, klabel('_i==_)]
             | Exp "i<" Exp [strict, klabel('_i<_)]

syntax Stmt ::= Id ":=" Exp [strict(2), klabel('_:=_)]
              | "skip" [klabel('skip)]
              | Stmt ";" Stmt [left, klabel('_;_)]
              | "if" Exp "then" Stmt "else" Stmt [strict(1), klabel
              ('if_then_else_)]
              | "while" Exp "do" Stmt [klabel('while_do_)]
              | "{" Stmt "}" [bracket, klabel('{_})]

syntax Code ::= Exp
              | Stmt

syntax KResult ::= Int
                 | Bool

rule <k2> I:Id => I1:Int ... </k2> <env> ... I |-> I1 ... </env>

rule I1:Int i+ I2:Int => I1 +Int I2

rule I1:Int i- I2:Int => I1 -Int I2

rule I1:Int i== I2:Int => I1 ==Int I2

rule I1:Int i< I2:Int => I1 <Int I2

rule <k2> I:Id := I1:Int => .K ... </k2> <env> ... I |-> ((_:K => I1)) ...
  </env>

rule <k2> I:Id := I1:Int => .K ... </k2> <env> Rho:Map ((.Map => I |-> I1))
  </env> when notBool (I in (keys (Rho)))

rule S1:Stmt ; S2:Stmt => S1 ~> S2

rule if true then S1:Stmt else _:K => S1

rule if false then _:K else S2:Stmt => S2

rule while E:Exp do S:Stmt => if E then (S ; (while E do S)) else skip




configuration
<agregation>
<first>
<t1> <k1> $PGM:K </k1> </t1></first>


<second>
<t2> <k2> $PGM:K </k2> <env> .Map </env> </t2></second>


</agregation>



endmodule
