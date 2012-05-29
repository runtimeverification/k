  // syntax AExp ::= Int | Id
  // 				| AExp "/" AExp [left, strict]
  // 				> AExp "+" AExp [left, strict]
  // 				| "(" AExp ")"  [bracket]

  // syntax BExp ::= Bool
  // 				| AExp "<=" AExp  [seqstrict]
  // 				| "not" BExp      [strict]
  // 				> BExp "and" BExp [left, strict(1)]
  // 				| "(" BExp ")"    [bracket]

  // syntax Stmt ::= "skip"
  // 				| Id ":=" AExp   [strict(2)]
  // 				| "if" BExp "then" Stmt "else" Stmt [strict(1)]
  // 				| "while" BExp "do" Stmt
  // 				> Stmt ";" Stmt   [left]
  // 				| "(" Stmt ")"    [bracket]


  // syntax Pgm ::= "var" Ids ";" Stmt
  // syntax Ids ::= List{Id, ","}
  // syntax Start ::= Pgm  

module IMP-FL-SYNTAX

  syntax KLabel ::= "div#ee"
  	 	  | "div#He"
  	 	  | "div#eH"
  	 	  | "plus#ee"
  	 	  | "plus#He"
  	 	  | "plus#eH"

		  | "le#ee"
		  | "le#He"

		  | "not#e"
		  | "not#H"

		  | "and#ee"
		  | "and#He"

		  | "assign#ee"
		  | "assign#eH"

		  | "ite#eee"
		  | "ite#Hee"

		  | "while#ee"

		  | "seq#ee"

		  | "pgm#ee"
		  
		  | "ids#"

		  | "start#e"

//   configuration <T color="yellow"> 
//   					<k color="green"> $PGM : K </k>
//   					<env color="red"> .Map </env>
//   				</T>

		  | "KCell#e"

		  | "EnvCell#e"

		  | "TCell#ee"

  syntax KResult ::= Int | Bool

endmodule

module IMP-FL
   imports IMP-FL-SYNTAX

// DIVISION

  rule 'KCell#e(('div#ee(E1,,E2) => E1 ~> 'div#He(E2)) ~> _)
       when 'notBool('isKResult(E1))

  rule 'KCell#e(('div#ee(E1,,E2) => E2 ~> 'div#eH(E1)) ~> _)
       when 'notBool('isKResult(E2))

  rule 'KCell#e((E1 ~> 'div#He(E2) => 'div#ee(E1,,E2)) ~> _)
       when 'isKResult(E1)

  rule 'KCell#e((E2 ~> 'div#eH(E1) => 'div#ee(E1,,E2)) ~> _)
       when 'isKResult(E2)

// PLUS

  rule 'KCell#e(('plus#ee(E1,,E2) => E1 ~> 'plus#He(E2)) ~> _)
       when 'notBool('isKResult(E1))

  rule 'KCell#e(('plus#ee(E1,,E2) => E2 ~> 'plus#eH(E1)) ~> _)
       when 'notBool('isKResult(E2))

  rule 'KCell#e((E1 ~> 'plus#He(E2) => 'plus#ee(E1,,E2)) ~> _)
       when 'isKResult(E1)

  rule 'KCell#e((E2 ~> 'plus#eH(E1) => 'plus#ee(E1,,E2)) ~> _)
       when 'isKResult(E2)

// LE

  rule 'KCell#e(('le#ee(E1,,E2) => E1 ~> 'le#He(E2)) ~> _)
       when 'notBool('isKResult(E1))

  rule 'KCell#e((E1 ~> 'le#He(E2) => 'le#ee(E1,,E2)) ~> _)
       when 'isKResult(E1)

// NOT

  rule 'KCell#e(('not#e(E1) => E1 ~> 'not#H(.List{K})) ~> _)
       when ''notBool('isKResult(E1))

  rule 'KCell#e((E1 ~> 'not#H(.List{K}) => 'not#e(E1)) ~> _)
       when 'isKResult(E1)

// AND

  rule 'KCell#e(('and#ee(E1,,E2) => E1 ~> 'and#He(E2)) ~> _)
       when 'notBool('isKResult(E1))

  rule 'KCell#e((E1 ~> 'and#He(E2) => 'and#ee(E1,,E2)) ~> _)
       when 'isKResult(E1)

// ASSIGN

  rule 'KCell#e(('assign#ee(E1,,E2) => E2 ~> 'assign#eH(E1)) ~> _)
       when 'notBool('isKResult(E2))

  rule 'KCell#e((E2 ~> 'assign#eH(E1) => 'assign#ee(E1,,E2)) ~> _)
       when 'isKResult(E2)

// ITE

  rule 'KCell#e(('ite#eee(E1,,E2,,E3) => E1 ~> 'ite#Hee(E2,,E3)) ~> _)
       when 'notBool('isKResult(E1))

  rule 'KCell#e((E1 ~> 'ite#Hee(E2,,E3) => 'ite#eee(E1,,E2,,E3)) ~> _)
       when 'isKResult(E1)

// ACTUAL RULES

//   rule [lookup] :  	<k> X:Id => I:Int ...</k>
//   					<env>... X |-> I ...</env> 
//   rule 'TCell#ee('KCell#e((X => I) ~> _),,'EnvCell('-Bag('Bag(X,,I),,_)))

//   rule [assignment]: <k> X:Id := I:Int => . ...</k>
//   					<env>... X |-> (_ => I) ...</env>
//   rule 'TCell#ee('KCell#e('assign#ee(X => I) ~> _),,'EnvCell('-Bag('Bag(X,,I),,_)))


//   rule [addition] : I1:Int + I2:Int => I1 +Int I2 
//   rule [div#ision] : I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0

//   rule [leq] : I1:Int <= I2:Int => I1 <=Int I2
//   rule [not] : not T:Bool => notBool T
//   rule [and-true] : true and B:BExp => B
//   rule [and-false]: false and B:BExp => false

//   rule [skip] : skip => .

//   rule [sequential] : S1;S2 => S1 ~> S2 [structural]

//   rule [if-true] : if true  then S else _ => S
//   rule [if-false]: if false then _ else S => S

//   rule [while] : <k> while B do S => if B then S ; while B do S else skip ...</k> [structural]

  // rule [program-still-vars]:
  // 	 	<k> var X:Id, Xs:Ids; S => var Xs; S ...</k>
  // 	    <env> Rho:Map (. => X |-> 0) </env> when notBool(X in keys(Rho))

//   rule [program-no-vars]: <k> var .Ids ; S => S ...</k> [structural]

endmodule
