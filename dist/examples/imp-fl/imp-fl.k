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

  syntax KResult ::= Int | Bool

endmodule

module IMP-FL
   imports IMP-FL-SYNTAX

// DIVISION

  rule div#ee(E1,,E2) => E1 ~> div#He(E2)
       when 'notBool('isKResult(E1))

  rule div#ee(E1,,E2) => E2 ~> div#eH(E1)
       when 'notBool('isKResult(E2))

  rule E1 ~> div#He(E2) => div#ee(E1,,E2) 
       when 'isKResult(E1)

  rule E2 ~> div#eH(E1) => div#ee(E1,,E2) 
       when 'isKResult(E2)

// PLUS

  rule plus#ee(E1,,E2) => E1 ~> plus#He(E2)
       when 'notBool('isKResult(E1))

  rule plus#ee(E1,,E2) => E2 ~> plus#eH(E1)
       when 'notBool('isKResult(E2))

  rule E1 ~> plus#He(E2) => plus#ee(E1,,E2) 
       when 'isKResult(E1)

  rule E2 ~> plus#eH(E1) => plus#ee(E1,,E2) 
       when 'isKResult(E2)

// LE

  rule le#ee(E1,,E2) => E1 ~> le#He(E2)
       when 'notBool('isKResult(E1))

  rule E1 ~> le#He(E2) => le#ee(E1,,E2) 
       when 'isKResult(E1)

// NOT

  rule not#e(E1) => E1 ~> not#H(.List{K})
       when 'notBool('isKResult(E1))

  rule E1 ~> not#H(.List{K}) => not#e(E1) 
       when 'isKResult(E1)

// AND

  rule and#ee(E1,,E2) => E1 ~> and#He(E2)
       when 'notBool('isKResult(E1))

  rule E1 ~> and#He(E2) => and#ee(E1,,E2) 
       when 'isKResult(E1)

// ASSIGN

  rule assign#ee(E1,,E2) => E2 ~> assign#eH(E1)
       when 'notBool('isKResult(E2))

  rule E2 ~> assign#eH(E1) => assign#ee(E1,,E2) 
       when 'isKResult(E2)

// ITE

  rule ite#eee(E1,,E2,,E3) => E1 ~> ite#Hee(E2,,E3)
       when 'notBool('isKResult(E1))

  rule E1 ~> ite#Hee(E2,,E3) => ite#eee(E1,,E2,,E3) 
       when 'isKResult(E1)


//   configuration <T color="yellow"> 
//   					<k color="green"> $PGM : K </k>
//   					<env color="red"> .Map </env>
//   				</T>


//   syntax KResult ::= Int | Bool

//   rule [lookup] :  	<k> X:Id => I:Int ...</k>
//   					<env>... X |-> I ...</env> 

//   rule [assignment]: <k> X:Id := I:Int => . ...</k>
//   					<env>... X |-> (_ => I) ...</env>

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
