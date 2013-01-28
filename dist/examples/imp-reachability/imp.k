require "builtins/symbolic-k.k"

module IMP-SYNTAX
  imports SYMBOLIC-K

  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > left:
		   AExp "+" AExp              [left, strict]
                 | AExp "-" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
		 > Stmt Stmt                  [left]
  syntax Pgm   ::= "int" Ids ";" Stmt
  syntax Ids   ::= List{Id,","}

  syntax Stmt ::= "#ps" "(" Bag ")"

  //@ K tool issues
  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]
  syntax Int ::= "(" Int ")" [bracket]
  syntax X ::= "symInt"  [dummySymInt]
  syntax Y ::= "symFreezeLabel"
  syntax priorities builtinWrapper > dummySymInt
endmodule

module IMP
  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
		 <goal multiplicity="*">
		  <k color="green"> #ps($PGM:Bag) </k>
                  <state color="blue"> .Map </state>
		  <condition color="red"> true </condition>
		  <frozen> none </frozen>
		 </goal>
                </T>
		

  syntax FreezeLabel ::= "none" | "#any"
  	 	       | "symFreezeLabel" "(" Int ")" //[onlyLabel, klabel(#symFreezeLabel)]

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
// BExp
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule ! T:Bool => notBool T
//  rule true && B => B
//  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1 S2 => S1 ~> S2  [structural]
//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [transition]
// Pgm
  rule <k> int (X:Id,Xs:Ids => Xs);_ </k> <state> Rho:Map (. => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]

//@ Symbolic execution - the transformed rules
  rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k>
       <condition> Phi:Bool => Phi andBool I2 =/=Int 0 </condition> 
       when checkSat(Phi andBool (I2 =/=Int 0)) =/=K "unsat" [transition]

  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Bool => Phi andBool B1 ==Bool true </condition> 
       when checkSat(Phi andBool B1) =/=K "unsat" [transition]
  
  rule <k> B1:Bool && B2:Bool => false ...</k>
       <condition> Phi:Bool => Phi andBool notBool B1 </condition> 
       when checkSat(Phi andBool notBool B1) =/=K "unsat" [transition]

  rule <goal>
         <k> if (B:Bool) S:Stmt else S':Stmt ~> K </k>
         <condition> Phi:Bool </condition> 
         <frozen> L </frozen>
         Cfg:Bag 
       </goal> 
       =>
       <goal>
         <k> S ~> K </k>
         <condition> Phi andBool B </condition> 
         <frozen> #any </frozen>
         Cfg 
       </goal>
       <goal>
         <k> S' ~> K </k>
         <condition> Phi andBool notBool(B) </condition> 
         <frozen> #any </frozen>
         Cfg
       </goal>
       when checkSat(Phi andBool B) =/=K "unsat"
       	    andBool checkSat(Phi andBool notBool B) =/=K "unsat" [transition, computational]

  rule <k> if (B:Bool) _ else S:Stmt => S ...</k>
       <condition> Phi:Bool </condition>
       <frozen> _ => #any </frozen>
       when checkSat(Phi andBool B) ==K "unsat" [transition, computational]

  rule <k> if (B:Bool) S:Stmt else _ => S ...</k>
       <condition> Phi:Bool </condition>
       <frozen> _ => #any </frozen>
       when checkSat(Phi andBool notBool B) ==K "unsat" [transition, computational]

// Generated rules
  syntax #Id ::= "a" | "b" | "x" | "y"
  rule (<k> while (y <= b) { b = b - y; a = a + 1; } ~> K </k>
       <state> a |-> A:Int b |-> B:Int x |-> X:Int y |-> Y:Int </state>
       <condition> F:Bool  </condition>
       =>
       <k> K </k>
       <state> a |-> A':Int b |-> B':Int x |-> X:Int y |-> Y:Int </state>
       <condition> F andBool 0 <=Int X andBool 0 <Int Y andBool X ==Int A' *Int Y +Int B' andBool B' >=Int 0 andBool B' <Int Y </condition>)
       <frozen> L:FreezeLabel </frozen>
       when fresh(B':Int) andBool fresh(A':Int)
       	    andBool (L =/=K symFreezeLabel(-1))
            andBool checkSat(F andBool notBool(0 <=Int X andBool 0 <Int Y andBool X ==Int A *Int Y +Int B andBool B >=Int 0)) ==K "unsat" [transition]

  rule (<k> { b = b - y; a = a + 1; } ~> K </k>
       <state> a |-> A:Int b |-> B:Int x |-> X:Int y |-> Y:Int </state>
       <condition> F:Bool  </condition>
       =>
       <k> K </k>
       <state> a |-> A':Int b |-> B':Int x |-> X:Int y |-> Y:Int </state>
       <condition> F andBool A' ==Int A +Int 1 andBool B' ==Int B -Int Y </condition>)
       <frozen> L:FreezeLabel </frozen>
       when fresh(B':Int) andBool fresh(A':Int)
       	    andBool (L =/=K symFreezeLabel(-2))
            andBool checkSat(F andBool notBool(true)) ==K "unsat" [transition]

  rule (<k> a = 0; b = x; while (y <= b) { b = b - y; a = a + 1; } ~> K </k>
       <state> a |-> A:Int b |-> B:Int x |-> X:Int y |-> Y:Int </state>
       <condition> F:Bool  </condition>
       =>
       <k> K </k>
       <state> a |-> A':Int b |-> B':Int x |-> X:Int y |-> Y:Int </state>
       <condition> F andBool 0 <=Int X andBool 0 <Int Y andBool X ==Int A' *Int Y +Int B' andBool B' >=Int 0 andBool B' <Int Y </condition>)
       <frozen> L:FreezeLabel </frozen>
       when fresh(B':Int) andBool fresh(A':Int)
       	    andBool (L =/=K symFreezeLabel(-1))
            andBool checkSat(F andBool notBool(0 <=Int X andBool 0 <Int Y andBool X ==Int A *Int Y +Int B andBool B >=Int 0)) ==K "unsat" [transition]

//@ Match
  syntax K ::= "match" "(" Bag ")"

  rule <k> match(
		<k> P </k>
		<state> Ma:Map  </state>
		<condition> Fa:Bool </condition>
//		<frozen> _ </frozen>
		)
	   => . //checkSat(Fc andBool (notBool Fa) andBool mapLeftEq(Ma, Mc))
       ...</k>
       <state> Mc:Map </state>
       <condition> Fc:Bool </condition>
       when checkSat(Fc andBool (notBool Fa) andBool mapLeftEq(Ma, Mc)) ==K "unsat"
       [transition]

//@ Utils
   rule (<k> #ps(B:Bag) </k>
   	<state> _ </state>
	<condition> _ </condition>
	<frozen> _ </frozen> ) => B [structural]

  syntax Bool ::= "mapLeftEq" "(" Map "," Map ")" [function]
  rule mapLeftEq(X:Id |-> V1:Int Rest:Map, Left:Map X |-> V2 Right:Map) => V1 ==Int V2 andBool mapLeftEq(Rest, Left Right)
  rule mapLeftEq(. , _) => true
  rule mapLeftEq(X:Id |-> _:Int _:Map, Right:Map) => false when notBool(X in keys(Right))
  rule mapLeftEq(M:Map, .) => false when notBool(isEmptySet(keys(M)))
 
endmodule