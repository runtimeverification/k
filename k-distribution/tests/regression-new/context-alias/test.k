module TEST
  imports INT
  imports ID
  imports MAP

configuration <k> $PGM:Stmt </k> <shouldHeat> false </shouldHeat> <state> .Map </state> <stuff> false </stuff>

context alias [heatable]: <k> HERE ...</k> <shouldHeat> true </shouldHeat>
context alias [heatable]: <k> HERE ...</k> <stuff> true </stuff>

context alias [heatable2]: <k> HERE ...</k> <shouldHeat> B </shouldHeat> requires B

syntax Expr ::= Expr "+" Expr [strict(heatable)]
              | Id "=" Expr [strict(heatable; 2)]
              | Id ":=" Expr [strict(2)]
              | Expr ":+" Expr [strict]
              | Expr "->+" Expr [seqstrict(heatable)]
              | Expr "-" Expr [seqstrict(heatable2)]
              | Int

syntax KResult ::= Int

syntax Stmt ::= Expr ";" [strict] | Stmt Stmt | enableHeating() | disableHeating()
syntax Expr ::= evalAndStop()

syntax Expr ::= "(" Expr ")" [bracket]

rule <k> enableHeating() => . ...</k> <shouldHeat> _ => true </shouldHeat>
rule <k> disableHeating() => . ...</k> <shouldHeat> _ => false </shouldHeat>

rule <k> evalAndStop() => 0 ...</k> <shouldHeat> _ => false </shouldHeat>

rule S::Stmt S2::Stmt => S ~> S2

rule I:Int ; => .K

rule <k> X:Id = I:Int => I ...</k> <state> Rho => Rho [ X <- I ] </state>
rule <k> X:Id := I:Int => I ...</k> <state> Rho => Rho [ X <- I ] </state>

rule I:Int + I2:Int => I +Int I2
rule I:Int :+ I2:Int => I +Int I2
rule I:Int ->+ I2:Int => I +Int I2

endmodule
