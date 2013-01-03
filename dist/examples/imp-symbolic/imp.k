require "builtins/symbolic-k.k"
require "builtins/fol.k"

module IMP-SYNTAX
  imports FOL

  syntax AExp  ::= Int | Id 
  	       	 | AExp "[" AExp "]"	      [strict]
                 > AExp "/" AExp              [left, strict]
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
                 | AExp "=" AExp ";"          [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
		 > Stmt Stmt                  [left]
  syntax Pgm   ::= "int" AExps ";" Stmt
  syntax AExps  ::= List{AExp,","}
  syntax Ids   ::= List{Id,","}

  //@ Assertions syntax
  syntax Stmt  ::= "assert" "(" BExp ")" ";"  [strict]

  /*@ Specifications: note that IMP symbolic programs consist in 
      symbolic configurations.
  */
  syntax CfgSym ::= "<k>" Stmt "</k>"
  	 	    "<env>" InitVals "</env>"
		    "<store>" InitVals "</store>"
		    "<condition>" Fol "</condition>"

  syntax InitVals ::= List{InitVal,","}
  syntax InitVal  ::= Id "->" AExp
  	 	    | Int "->" AExp

  // syntax for symbolic values in programs
  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]
  syntax Array ::=  "#symArray" "(" Id ")" [onlyLabel, klabel(#symArray)]

  syntax Val ::= Int | Bool | Array
  	       | "array" "(" Int "," Int ")" 
	       | "loc" "(" AExp ")"
  syntax AExp ::= Val

endmodule

module IMP
  imports IMP-SYNTAX
  imports ARRAY

  syntax KResult ::= Val

/*@ IMP configuration is enriched with cell {\tt condition}. */
  configuration <T color="yellow">
		  <k color="green"> $PGM:CfgSym </k>
                  <env color="blue"> .Map </env>
		  <store color="orange"> .Map </store> 
		  <condition color="red"> true </condition>
                </T>

// Array element: evaluate the array and its index; 
// then the array lookup rule above applies.
  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

// AExp
  rule <k> X:Id => V ...</k> <env>... X |-> L ...</env> <store>... L:Int |-> V:Val </store>
  rule <k> array(L:Int, Size:Int)[I:Int] => lookup(L +Int I) ...</k>
       <store>... L |-> V:#Int ...</store>
 
  rule <k> array(L:Int, Size:Int)[I:Int] => select(A, I) ...</k>
       <store>... L |-> A:Array ...</store>

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

// lvalue
  syntax AExp ::= "lvalue" "(" K ")"

// Local variable                                                                                        
  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

// lookup
  syntax K ::= "lookup" "(" Int ")"
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

// Stmt
  context (HOLE => lvalue(HOLE)) = _;
  rule <k> loc(L:Int) = I:Int; => . ...</k> <store>... L |-> (_ => I) ...</store>
  rule <k> lvalue(array(L:Int, Size:Int)[I:Int]) => loc(L +Int I) ...</k> 
       <store>... L |-> V:#Int ...</store>

  rule <k> loc(array(L:Int, Size:Int)[I:Int]) = V:Val; => . ...</k> 
       <store>... L |-> (A:Array => store(A, I, V)) ...</store>
   
  rule S1 S2 => S1 ~> S2  [structural]
//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X:Id,Xs:AExps => Xs);_ </k> 
       <env> Rho:Map (. => X |-> L) </env>
       <store>... . => (L |-> 0) </store>
    when notBool (X in keys(Rho)) andBool fresh(L:Int)
  rule int .AExps; S => S  [structural]

/*@ The symbolic semantics of IMP. Note that these rules can be automatically generated from concrete ones applying three steps:
\begin{itemize}
\item Linearise rules: each variable should appear only once in the left hand side of the rule
\item Replace constant values {\it C} with variables {\it V} and add a side condition to the rule: {\it V = C}.
\item Add formulas as side conditions when the conjuntion of the formula and rule condition is not {\tt unsat}.
\end{itemize}
 */
  rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k>
       <condition> Phi:Fol => Phi andFol I2 =/=Int 0 </condition> 
       when checkSat(Phi andFol (I2 =/=Int 0)) =/=K "unsat" [transition]

  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Fol => Phi andFol B1 ==Bool true </condition> 
       when checkSat(Phi andFol B1) =/=K "unsat" [transition]
  
  rule <k> B1:Bool && B2:Bool => false ...</k>
       <condition> Phi:Fol => Phi andFol notFol B1 </condition> 
       when checkSat(Phi andFol notFol B1) =/=K "unsat" [transition]

  rule <k> if (B:Bool) S:Stmt else _ => S ...</k>
       <condition> Phi:Fol => Phi andFol B </condition> 
       when checkSat(Phi andFol B) =/=K "unsat" [transition]

  rule <k> if (B:Bool) _ else S:Stmt => S ...</k>
       <condition> Phi:Fol => Phi andFol notFol B </condition>
       when checkSat(Phi andFol notFol B) =/=K "unsat" [transition]

/*@ Assert semantics: remain stuck when the assertion doesn' hold. */
  rule <k> assert(B:BExp); => . ...</k>
       <condition> Phi:Fol </condition> 
       when checkSat(Phi andFol transformBool(B)) ==K "sat" 

/*@ Loading the initial program into a configuration */
  rule [initial]:   <k>
			<k> Program:Stmt </k>
			<env> InitVs:InitVals </env>
			<store> InitVs':InitVals </store>
			<condition> Formula:Fol </condition> 
			=> initialize1(InitVs) ~> initialize2(InitVs') ~> Program
		    </k>
		    <condition> _ => Formula </condition>  

//@ Load the environment.
  syntax K ::= "initialize1" "(" InitVals ")"
  	     | "initialize2" "(" InitVals ")"

  rule initialize1(.InitVals) => . [structural]
  rule <k> initialize1(X:Id -> I:AExp, Vs:InitVals) => initialize1(Vs) ...</k>
       <env>... . => X |-> I </env> [structural]

  rule initialize2(.InitVals) => . [structural]
  rule <k> initialize2(X:Int -> I:AExp, Vs:InitVals) => initialize2(Vs) ...</k>
       <store>... . => X |-> I </store> [structural]

//@ Transform BExp formulas into internal representation for formulas.
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

  rule isSymbolicInt(select(A:Array, I:Int)) => true [anywhere]
  rule isInt(select(A:Array, I:Int)) => true [anywhere]
  rule lvalue(array(I:Int, S:Int)[V:Int]) => lvalue(loc(array(I:Int, S:Int)[V:Int]))

endmodule