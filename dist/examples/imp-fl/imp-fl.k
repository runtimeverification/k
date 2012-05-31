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
		  
		  | "emptyIds#"
		  
		  | "consIds#ee"

	    | "skip#"

  syntax Val ::= Int | Bool

  syntax KResult ::= Val

endmodule

module IMP-FL
   imports IMP-FL-SYNTAX

   configuration <T color="yellow"> 
   					<k color="green"> $PGM : K </k>
   					<env color="red"> .Map </env>
   				</T>

// DIVISION


  
  rule <k> div#ee(E1,,E2) ~> K:K </k>
       =>
       <k>E1 ~> div#He(E2) ~> K </k>
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

  rule <T>
          <k> X:Id ~> K:K </k>
          <env> EL:Map X |-> I ER:Map </env>
       </T>
       =>
       <T>
          <k> I ~> K </k>
          <env> EL X |-> I ER </env> 
       </T>

//   rule [assignment]: <k> X:Id := I:Int => . ...</k>
//   					<env>... X |-> (_ => I) ...</env>

  rule <T>
          <k> assign#ee(X:Id,,I:Int) ~> K:K </k>
          <env> EL:Map X |-> _ ER:Map </env>
       </T>
       =>
       <T>
          <k> K </k>
          <env> EL X |-> I ER </env> 
       </T>

//   rule [addition] : I1:Int + I2:Int => I1 +Int I2 

  rule <k> plus#ee(I1:Int,,I2:Int) ~> K:K </k>
       =>
       <k> I1 +Int I2 ~> K </k>

//   rule [div#ision] : I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0

  rule <k> div#ee(I1:Int,,I2:Int) ~> K:K </k>
       =>
       <k> I1 /Int I2 ~> K </k>
     when I2 =/=K 0

//   rule [leq] : I1:Int <= I2:Int => I1 <=Int I2

  rule <k> leq#ee(I1:Int,,I2:Int) ~> K:K </k>
       =>
       <k> I1 <=Int I2 ~> K </k>

//   rule [not] : not T:Bool => notBool T

  rule <k> not#e(B:Bool) ~> K:K </k>
       =>
       <k> notBool B ~> K </k>

//   rule [and-true] : true and B:BExp => B

  rule <k> and#ee(true,,B:Bool) ~> K:K </k>
       =>
       <k> B ~> K </k>

//   rule [and-false]: false and B:BExp => false

  rule <k> and#ee(false,,_:K) ~> K:K </k>
       =>
       <k> false ~> K </k>

//   rule [skip] : skip => .

  rule <k> skip#(.List{K}) ~> K:K </k>
       =>
       <k> K </k>

//   rule [sequential] : S1;S2 => S1 ~> S2 [structural]

  rule <k> seq#ee(E1:K,,E2:K) ~> K:K </k>
       =>
       <k> E1 ~> E2 ~> K </k>

//   rule [if-true] : if true  then S else _ => S

  rule <k> ite#eee(true,,E1:K,,E2:K) ~> K:K </k>
       =>
       <k> E1 ~> K </k>

//   rule [if-false]: if false then _ else S => S

  rule <k> ite#eee(false,,E1:K,,E2:K) ~> K:K </k>
       =>
       <k> E2 ~> K </k>

//   rule [while] : <k> while B do S => if B then S ; while B do S else skip ...</k> [structural]

  rule <k> while#ee(E:K,,S:K) ~> K:K </k>
       =>
       <k> ite#eee(E,,seq#ee(S,,while#ee(E:K,,S:K)),,skip#) ~> K </k>

  // rule [program-still-vars]:
  // 	 	<k> var X:Id, Xs:Ids; S => var Xs; S ...</k>
  // 	    <env> Rho:Map (. => X |-> 0) </env> when notBool(X in keys(Rho))

  rule <T>
          <k> consIds(V:K,,Rest::K) ~> K:K </k>
          <env> E:Map </env>
       </T>
       =>
       <T>
          <k> K </k>
          <env> X |-> 0 E </env> 
       </T>
     when 'notBool(X in keys(E))

//   rule [program-no-vars]: <k> var .Ids ; S => S ...</k> [structural]

endmodule
