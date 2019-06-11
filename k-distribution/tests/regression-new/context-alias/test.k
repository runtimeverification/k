module TEST
  imports INT
  imports ID
  imports MAP

configuration <k> $PGM:K </k> <shouldHeat> false </shouldHeat> <state> .Map </state>

context alias [heatable]: <k> HERE ...</k> <shouldHeat> true </shouldHeat>

syntax Expr ::= Expr "+" Expr [strict(heatable)]
              | Id "=" Expr [strict(heatable; 2)]
              | Id ":=" Expr [strict(2)]
              | Expr ":+" Expr [strict]
              | Expr "->+" Expr [seqstrict(heatable)]
              | Int

syntax KResult ::= Int

syntax Stmt ::= Expr ";" [strict] | Stmt Stmt | enableHeating() | disableHeating()

rule <k> enableHeating() => . ...</k> <shouldHeat> _ => true </shouldHeat>
rule <k> disableHeating() => . ...</k> <shouldHeat> _ => false </shouldHeat>

rule S::Stmt S2::Stmt => S ~> S2

rule I:Int ; => .K

rule <k> X:Id = I:Int => I ...</k> <state> Rho => Rho [ X <- I ] </state>
rule <k> X:Id := I:Int => I ...</k> <state> Rho => Rho [ X <- I ] </state>

rule I:Int + I2:Int => I +Int I2
rule I:Int :+ I2:Int => I +Int I2
rule I:Int ->+ I2:Int => I +Int I2

endmodule
