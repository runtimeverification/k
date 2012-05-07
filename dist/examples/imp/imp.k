require "k-prelude.k"

module IMP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS 
  
  syntax AExp ::= Int | Id
  				| AExp "/" AExp [left, strict]
  				> AExp "+" AExp [left, strict]
  				| "(" AExp ")"  [bracket]

  syntax BExp ::= Bool
  				| AExp "<=" AExp  [seqstrict]
  				| "not" BExp      [strict]
  				> BExp "and" BExp [left, strict(1)]
  				| "(" BExp ")"    [bracket]

  syntax Stmt ::= "skip"
  				| Id ":=" AExp   [strict(2)]
  				| "if" BExp "then" Stmt "else" Stmt [strict(1)]
  				| "while" BExp "do" Stmt
  				> Stmt ";" Stmt   [left]
  				| "(" Stmt ")"    [bracket]

  syntax Pgm ::= "var" Ids ";" Stmt
  syntax Ids ::= List{Id, ","}
  syntax Start ::= Pgm  
endmodule


module IMP
  imports IMP-SYNTAX
  imports BUILTIN-HOOKS
  imports K

  configuration <T> 
  					<k> $PGM : K </k>
  					<env> .Map </env>
  				</T>


  syntax KResult ::= Int | Bool

  rule [lookup] :  	<k> X:Id => I:Int ...</k>
  					<env>... X |-> I ...</env> 

  rule [assignment]: <k> X:Id := I:Int => . ...</k>
  					<env>... X |-> (_ => I) ...</env>

  rule [addition] : I1:Int + I2:Int => I1 +Int I2 
  rule [division] : I1:Int / I2:Int => I1 /Int I2 when I2 =/=Bool 0

  rule [leq] : I1:Int <= I2:Int => I1 <=Int I2
  rule [not] : not T:Bool => notBool T
  rule [and-true] : true and B:BExp => B
  rule [and-false]: false and B:BExp => false

  rule [skip] : skip => .

  rule [sequential] : S1;S2 => S1 ~> S2 [structural]

  rule [if-true] : if true  then S else _ => S
  rule [if-false]: if false then _ else S => S

  rule [while] : <k> while B do S => if B then S ; while B do S else skip ...</k> [structural]


  rule [program-still-vars]:
  	 	<k> var X:Id, Xs:Ids; S => var Xs; S ...</k>
  	    <env> Rho:Map (. => X |-> 0) </env> when notBool(X in keys(Rho))

  rule [program-no-vars]: <k> var .Ids ; S => S ...</k> [structural]

endmodule
