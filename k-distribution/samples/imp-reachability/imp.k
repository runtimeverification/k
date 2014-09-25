// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*@

This is the symbolic semantics of IMP enriched with reachability logic.

This semantics receives as input programs generated from reachability formulas.
Additionally, the semantics contains the circularities also generated from
reachability formulas.
*/

module IMP-SYNTAX

  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > left:
           AExp "+" AExp              [left, strict]
                 | AExp "-" AExp              [left, strict]
                 > "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
                 | Id ":" Block
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
                 > Id ":" Stmt
  syntax Pgm   ::= "int" Ids ";" Stmt
  syntax Ids   ::= List{Id,","}

  syntax Pgm ::= "#ps" "(" TCellFragment ")"

  //@ K tool issues
  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]
  syntax Int ::= "(" Int ")" [bracket]
  syntax X ::= "symInt"  [dummySymInt]
//  syntax Y ::= "symFreezeLabel"


endmodule

module IMP
  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool
/*@
The configuration of IMP is enriched with cells <frozen> and <goal>.
Cell <ruleConstraints> will store some labels which are meant to block
the first application of the circularity rule.
The cell <goal> contains the current goal. Whenever multiple rules can be
applied to the same configuration, the current goal will be splitted into
multiple goals.
*/
  configuration <T color="yellow" multiplicity="?">
//         <goal multiplicity="*">
          <k color="green"> #ps($PGM:Bag) </k>
                  <state color="blue"> .Map </state>
          <condition color="red"> true </condition>
//          <ruleConstraints> none </ruleConstraints>
//         </goal>
                </T>
        <success> false </success>


/*@
The initial semantics of IMP.
*/
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
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [transition]
// Pgm
  rule <k> int (X:Id,Xs:Ids => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]

//@ Symbolic semantics - the transformed rules
  rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k>
       <condition> Phi:Bool => Phi andBool I2 =/=Int 0 </condition>
       when checkSat(Phi andBool (I2 =/=Int 0)) =/=K "unsat" [transition]

  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Bool => Phi andBool B1 ==Bool true </condition>
       when checkSat(Phi andBool B1) =/=K "unsat" [transition]

  rule <k> B1:Bool && B2:Bool => false ...</k>
       <condition> Phi:Bool => Phi andBool notBool B1 </condition>
       when checkSat(Phi andBool notBool B1) =/=K "unsat" [transition]

  rule <k> if (B:Bool) S else _ => S ...</k>
       <condition> Phi:Bool => Phi andBool B </condition>
       when checkSat(Phi andBool B) =/=K "unsat" [transition, computational]

  rule <k> if (B:Bool) _ else S => S ...</k>
       <condition> Phi:Bool => Phi andBool notBool B </condition>
       when checkSat(Phi andBool notBool B) =/=K "unsat" [transition, computational]


/*@ These rules must be generated from reachability formulas given as input
and added to the semantics at runtime. Since we don't have this posibility now,
we added them manually

For each reachability formula given as input we have two corresponding generated rules:
 - one corresponding to circularity deduction rule
 - one checking if the final configuration implies the righ-hand side of the formula
   (corresponding to consequece deduction rule).
*/

  syntax Id ::= Token{"a"} | Token{"b"} | Token{"x"} | Token{"y"}
              | Token{"ll0"} | Token{"ll1"} | Token{"ll2"}

  syntax Pgm ::= "check0" | "check1" | "check2"   // one for each formula

  syntax Bag ::= "success"

  rule (<k> (ll0 : (a = 0; b = x; (ll1 : while (y <= b) { b = b - y; a = a + 1; }))) ~> K:K </k>
       <state> a |-> A:Int b |-> B:Int x |-> X:Int y |-> Y:Int </state>
       <condition> Psi:Bool  </condition>
       =>
       <k> K </k>
       <state> a |-> !A':Int b |-> !B':Int x |-> X:Int y |-> Y:Int </state>
       <condition> Psi andBool 0 <=Int X andBool 0 <Int Y </condition>)
       when checkSat(Psi andBool notBool(0 <=Int X andBool 0 <Int Y)) ==K "unsat"
      [transition]

  rule (<T>
         <k> check0 </k>
         <state> a |-> A':Int b |-> B':Int x |-> X:Int y |-> Y:Int </state>
         <condition> Psi:Bool </condition>
       </T>
       =>
       .)
       <success> _ => true </success>
       when checkSat(Psi andBool
                     notBool ((X ==Int A' *Int Y +Int B' andBool B' >=Int 0 andBool B' <Int Y)))
            ==K "unsat"
       [transition]

  rule (<k> (ll1 : while (y <= b) ({ b = b - y; a = a + 1; })::Block)::Stmt ~> K:K </k>
       <state> a |-> A:Int b |-> B:Int x |-> X:Int y |-> Y:Int </state>
       <condition> Psi:Bool  </condition>
       =>
       <k> K </k>
       <state> a |-> !A':Int b |-> !B':Int x |-> X:Int y |-> Y:Int </state>
       <condition>
         Psi andBool
         X ==Int !A' *Int Y +Int !B' andBool !B' >=Int 0 andBool !B' <Int Y
       </condition>)
       when checkSat(Psi andBool notBool(X ==Int A *Int Y +Int B andBool B >=Int 0))
                    ==K "unsat"
      [transition]

  rule (<T>
         <k> check1 </k>
         <state> a |-> A':Int b |-> B':Int x |-> X:Int y |-> Y:Int </state>
         <condition> Psi:Bool </condition>
       </T>
       =>
    .)
       <success> _ => true </success>
       when checkSat(Psi andBool
                     notBool (X ==Int A' *Int Y +Int B' andBool B' >=Int 0 andBool B' <Int Y))
            ==K "unsat"
       [transition]

  rule (<k> (ll2 : { b = b - y; a = a + 1; })::Block ~> K </k>
       <state> a |-> A:Int b |-> B:Int x |-> X:Int y |-> Y:Int </state>
       <condition> Psi:Bool  </condition>
       =>
       <k> K </k>
       <state> a |-> !A':Int b |-> !B':Int x |-> X:Int y |-> Y:Int </state>
       <condition>
         Psi andBool
         (X ==Int !A' *Int Y +Int !B' andBool !B' >=Int 0)
       </condition>)
       when checkSat(Psi andBool
                             notBool (X ==Int A *Int Y +Int B andBool B >=Int 0 andBool Y <=Int B))
                    ==K "unsat"
       [transition]

  rule (<T>
         <k> check2 </k>
         <state> a |-> A':Int b |-> B':Int x |-> X:Int y |-> Y:Int </state>
         <condition> Psi:Bool </condition>
       </T>
       =>
    .)
       <success> _ => true </success>
       when checkSat(Psi andBool
                     notBool (X ==Int A' *Int Y +Int B' andBool B' >=Int 0))
            ==K "unsat"
       [transition]

//@ Utils
   rule (<k> #ps(B:Bag) </k>
       <state> _ </state>
    <condition> _ </condition>) => B [structural]

endmodule
