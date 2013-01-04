require "builtins/symbolic-k.k"
require "builtins/fol.k"

module IMP-SYNTAX
  imports FOL

  syntax AExp  ::= Int | Id
                 > left:
		   AExp "*" AExp              [left, strict]
                 | AExp "/" AExp              [left, strict]
                 > left:
		   AExp "+" AExp              [left, strict]
                 | AExp "-" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | AExp "==" AExp             [strict]
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

  syntax Stmt ::= "while " "(" BExp ")" "invariant" ":" Assert Block
  syntax Assert ::= BExp
  	 	  | Assert "and" Assert [strict]
		  | Assert "or" Assert  [strict]
		  | "not" Assert        [strict]
  syntax Pre   ::= "pre"  ":" Assert
  syntax Post  ::= "post" ":" Assert
  syntax Program ::= "int" Ids ";" Pre Post Stmt
endmodule

module IMP
  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
		  <k color="green"> $PGM:Program </k>
                  <state color="blue"> .Map </state>
		  <condition color="red"> true </condition>
                </T>

//@ IMP concrete semantics
// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
// BExp
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int == I2:Int => I1 ==Int I2
  rule ! T:Bool => notBool T
//  rule true && B => B
//  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <T> <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state> ...</T>
  rule S1 S2 => S1 ~> S2  [structural]
//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X:Id,Xs:Ids => Xs); _ </k> <state> Rho:Map (. => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S:Stmt => S  [structural]


//@ IMP symbolic semantics
  rule <T> <k> I1:Int / I2:Int => I1 /Int I2 ...</k>
       <condition> Phi:Fol => Phi andFol I2 =/=Int 0 </condition> ...</T>
       when checkSat(Phi andFol (I2 =/=Int 0)) ==K "sat" [transition]

  rule <T> <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Fol => Phi andFol B1 ==Bool true </condition> ...</T>
//       when checkSat(Phi andFol B1) ==K "sat" [transition]
  
  rule <T> <k> B1:Bool && B2:Bool => false ...</k>
       <condition> Phi:Fol => Phi andFol notFol B1 </condition> ...</T>
//       when checkSat(Phi andFol notFol B1) ==K "sat" [transition]

  rule <T> <k> if (B:Bool) S:Stmt else _ => S ...</k>
       <condition> Phi:Fol => Phi andFol B </condition> ...</T>
       when checkSat(Phi andFol B) ==K "sat" [transition]

  rule <T> <k> if (B:Bool) _ else S:Stmt => S ...</k>
       <condition> Phi:Fol => Phi andFol notFol B </condition> ...</T>
       when checkSat(Phi andFol notFol B) ==K "sat" [transition]

//@ Specifications
  rule <k> int (X:Id,Xs:Ids => Xs); _:Pre _:Post _:Stmt </k>
       <state> Rho:Map (. => X |-> 0) </state>
       when notBool (X in keys(Rho)) 
  rule int .Ids ; P:Pre P':Post S:Stmt => P ~> P' ~> S [structural]

//@ Hoare triples
  rule <k> (pre: Psi:Assert ~> post: Psi':Assert ~> S:Stmt)
            =>
            assume(Psi) ~> S ~> match(A2M(Psi'))
       </k>
       <state> M:Map </state>
       [transition]

//@ {\tt assume} and {\tt match}
  syntax K ::= "assume" "(" K ")"
	     | "assumeStrict" "(" K ")" [strict]

//@ Assume
  rule assume(Psi:K) => assumeStrict(A2M(Psi))

  rule <k> assumeStrict(m2k(E:Map, Phi:K)) => . ...</k>
       <state> _ => E </state>
       <condition> _ => Phi </condition>
       [transition]

//@ Match
  syntax K ::= "match"  "(" K ")" [strict]
//  rule <k> match(Phi) => A2M(Phi) ...</k>

//@ Match
  rule <k> match(m2k(Ea:Map, Phia:K))
	   => . // checkSat(Phic andFol (notFol Phia) andFol mapLeftEq(Ea, Ec))
       ...</k>
       <state> Ec:Map </state>
       <condition> Phic:Fol </condition>
       when checkSat(Phic andFol (notFol Phia) andFol mapLeftEq(Ea, Ec))
            ==K
            "unsat"
       [transition]

//@ While invariant
  rule <k> while ( B:BExp ) invariant: Psi:Assert S:Stmt ~> K
           =>
           assume(Psi and B) ~> match(A2M(Psi))
       </k>
//       <state> M:Map </state> 
  [transition]

  rule <k> while ( B:BExp ) invariant: Psi:Assert S:Stmt ~> K
           => match(A2M(Psi)) ~> assume(Psi and not B)
       </k>
//       <state> M:Map </state> 
  [transition]

//@ A2M
  syntax K ::= "A2M" "(" K ")"

  rule <k> A2M(Psi)
           =>
           generateFresh(E) ~> evalAssert(Psi) ~> restore(E, Phi)
       ...</k>
       <state> E:Map </state>
       <condition> Phi:Fol </condition>
       [transition]

//@ Generate fresh map
  syntax K ::= "generateFresh" "(" Map ")"
  rule <k> generateFresh(X:Id |-> V:Int E:Map) => generateFresh(E) ...</k>
       <state>... X |-> (V => V') ...</state> when fresh(V':Int)
  rule <k> generateFresh(.Map) => . ...</k>

//@ Assert evaluation
  syntax K ::= "evalAssert" "(" K ")" [strict]
  syntax KResult ::= "m2k" "(" Map "," K ")"

  rule <k> evalAssert(Phi:K) ~> restore(E':Map, Phi':K)
           =>
           m2k(E, Phi) 
       ...</k>
       <state> E:Map => E' </state>
       <condition> _ => Phi' </condition>
       [transition]


//@ Restore
  syntax K ::= "restore" "(" Map "," Fol ")"

//@ Ignore strictness
//  context B && HOLE
//  context B andBool HOLE

//@ Assertions
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1:Bool  or B2:Bool => B1  orBool B2
  rule not B:Bool => notBool B


//@ Utils       
       
  syntax Bool ::= "mapLeftEq" "(" Map "," Map ")" [function]
  rule mapLeftEq(X:Id |-> V1:Int Rest:Map, Left:Map X |-> V2 Right:Map) => V1 ==Int V2 andBool mapLeftEq(Rest, Left Right)
  rule mapLeftEq(. , _) => true
  rule mapLeftEq(X:Id |-> _:Int _:Map, Right:Map) => false when notBool(X in keys(Right))
  rule mapLeftEq(M:Map, .) => false when notBool(isEmptySet(keys(M)))
endmodule