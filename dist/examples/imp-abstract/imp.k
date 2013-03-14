/*@
This is the abstract semantics of IMP. It contains the normal semantics of IMP
and its extension for abstact execution. 
*/

module ABSTRACT-DOMAIN-SYNTAX
  syntax Int ::= "anyInt"
  syntax Bool ::= "anyBool"
endmodule

module IMP-SYNTAX
  imports ABSTRACT-DOMAIN-SYNTAX


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
endmodule


module ABSTRACT-DOMAIN
  imports ABSTRACT-DOMAIN-SYNTAX
  syntax Bool ::= K "generalizes" K [function]
  rule B:Bool generalizes B => true
  rule I:Int generalizes I => true
  rule anyBool generalizes _:Bool => true
  rule anyInt generalizes I:Int => true

  syntax Int ::= Int "plusInt" Int [function]

  rule anyInt plusInt _:Int => anyInt   
  rule _:Int plusInt anyInt => anyInt   
 
  rule I1:Int plusInt I2:Int => #if I1 +Int I2 <=Int 10 ==K true #then  I1 +Int I2 #else anyInt #fi 

  rule anyInt divInt I:Int => anyInt  when I =/=Int 0 
  rule _:Int divInt anyInt => anyInt   

  rule anyInt <=Int _:Int => anyBool   
  rule _:Int <=Int anyInt => anyBool   

  rule anyInt ==Int _:Int => anyBool   
  rule _:Int ==Int anyInt => anyBool   

  rule anyInt =/=Int _:Int => anyBool   
  rule _:Int =/=Int anyInt => anyBool

  rule anyBool ==Bool _:Bool => anyBool   
  rule _:Bool ==Bool anyBool => anyBool   

  rule false andBool B:Bool => false
  rule B:Bool andBool false => false

  rule anyBool andBool B:Bool => anyBool  when B =/=Bool false 
//  rule B:Bool andBool anyBool) => anyBool  when B =/=Bool false 
  rule '_andBool_(B:Bool,, anyBool) => anyBool  when B =/=Bool false 

  rule true orBool B:Bool => true
  rule B:Bool orBool true => true

  rule anyBool orBool B:Bool => anyBool  when B =/=Bool true 
  rule '_orBool_(B:Bool,, anyBool) => anyBool  when B =/=Bool true 

  rule notBool anyBool => anyBool
endmodule

module IMP
  imports IMP-SYNTAX
  imports ABSTRACT-DOMAIN

  syntax KResult ::= Int | Bool

/*@ IMP configuration is enriched with cell {\tt condition}. */
  configuration <T color="yellow">
		  <k color="green"> $PGM:Pgm </k>
                  <state color="blue"> .Map </state>
                </T>

/*@ The concrete semantics of IMP which remains unchanged for symbolic execution */
// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
//  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 plusInt I2
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

//@ IMP symbolic semantics
  rule <k> I1:Int / I2:Int => I1 divInt I2 ...</k>
       when (I2 =/=Int 0) generalizes true [transition]

  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       when (B1 ==Bool true) generalizes true  [transition]
  
  rule <k> B1:Bool && B2:BExp => false ...</k>
       when (B1 ==Bool false) generalizes true  [transition]

  rule <k> if (B:Bool) S:Stmt else _ => S ...</k>
       when (B ==Bool true) generalizes true  [transition]

  rule <k> if (B:Bool) _ else S:Stmt => S ...</k>
       when (B ==Bool false) generalizes true  [transition]

  rule <k> int (X:Id,Xs:Ids => Xs);_ </k> <state> Rho:Map (. => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]

endmodule
