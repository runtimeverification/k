require "builtins/symbolic-k.k"
require "builtins/fol.k"

module IMP-SYNTAX
  imports FOL

  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
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

  // assertions
  syntax Stmt  ::= "assert" "(" BExp ")" ";"  [strict]

  // specifications
  syntax InitVals ::= List{InitVal,","}
  syntax InitVal  ::= Id "->" Int

  syntax CfgSym ::= "<k>" Stmt "</k>"
  	 	    "<env>" InitVals "</env>"
		    "<condition>" Fol "</condition>"

  // syntax for symbolic values in programs
  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]

endmodule

module IMP
  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
		  <k color="green"> $PGM:CfgSym </k>
                  <state color="blue"> .Map </state>
		  <condition color="red"> true </condition>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
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
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X:Id,Xs:Ids => Xs);_ </k> <state> Rho:Map (. => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]

// the transformed rules
  rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k>
       <condition> Phi:Fol => Phi andFol I2 =/=Int 0 </condition> 
       when checkSat(Phi andFol (I2 =/=Int 0)) ==K "sat" [transition]

  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Fol => Phi andFol B1 ==Bool true </condition> 
       when checkSat(Phi andFol B1) ==K "sat" [transition]
  
  rule <k> B1:Bool && B2:Bool => false ...</k>
       <condition> Phi:Fol => Phi andFol notFol B1 </condition> 
       when checkSat(Phi andFol notFol B1) ==K "sat" [transition]

  rule <k> if (B:Bool) S:Stmt else _ => S ...</k>
       <condition> Phi:Fol => Phi andFol B </condition> 
       when checkSat(Phi andFol B) ==K "sat" [transition]

  rule <k> if (B:Bool) _ else S:Stmt => S ...</k>
       <condition> Phi:Fol => Phi andFol notFol B </condition>
       when checkSat(Phi andFol notFol B) ==K "sat" [transition]

// assert
  rule <k> assert(B:BExp); => . ...</k>
       <condition> Phi:Fol </condition> 
       when checkSat(Phi andFol transformBool(B)) ==K "sat" 

// setting up the initial configuration
  rule [initial]:   <k>
			<k> Program:Stmt </k>
			<env> InitVs:InitVals </env>
			<condition> Formula:Fol </condition> 
			=> initialize(InitVs) ~> Program
		    </k>
		    <condition> _ => Formula </condition>  

// load the environment
  syntax K ::= "initialize" "(" InitVals ")"

  rule initialize(.InitVals) => . [structural]
  rule <k> initialize(X:Id -> I:Int, Vs:InitVals) => initialize(Vs) ...</k>
       <state>... . => X |-> I </state> [structural]

// transform the formula into an internal format
  syntax Int ::= "transformInt" "(" AExp ")" [function]
  rule transformInt(I:Int) => I
  rule transformInt(X:Id)  => #symInt(X)
  rule transformInt(A1:AExp + A2:AExp) => transformInt(A1) +Int transformInt(A2)
  rule transformInt(A1:AExp / A2:AExp) => transformInt(A1) /Int transformInt(A2)


  syntax Bool ::= "transformBool" "(" BExp ")" [function]
  rule transformBool(true) => true
  rule transformBool(false) => false
  rule transformBool(A1:AExp <= A2:AExp) => transformInt(A1) <=Int transformInt(A2)
  rule transformBool(B1:BExp && B2:BExp) => transformBool(B1) andBool transformBool(B2)
  rule transformBool(! B:BExp) => notBool transformBool(B)

  rule transformBool(B:Bool) => B

endmodule