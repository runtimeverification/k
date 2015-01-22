// Copyright (c) 2014-2015 K Team. All Rights Reserved.
/*@
This is the symbolic semantics of IMP. It contains the normal semantics if IMP
and the rules for symbolic execution, as described in the technical report
available here: https://fmse.info.uaic.ro/publications/156/ .
*/
module IMP-SYNTAX

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

  //@ Programs are \K configurations.
  syntax Stmt  ::= "#ps" "(" TCellFragment ")"

  //@ Assertions syntax
  syntax Stmt  ::= "assert" "(" BExp ")" ";"  [strict]

  //@ \K compiler issues
  syntax Dummy ::= "symInt" [dummySymInt]
  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]

  // hack for parsing the ids below in the specifications
  syntax Id ::= Token{"a"} | Token{"b"} | Token{"c"}
              | Token{"sum"} | Token{"i"} | Token{"n"}
              | Token{"x"} | Token{"min"}
endmodule

module IMP
  imports IMP-SYNTAX
  imports FREE-VARS

  syntax KResult ::= Int | Bool

/*@ IMP configuration is enriched with cell {\tt condition}. */
  configuration <T color="yellow">
          <k color="green"> #ps($PGM:Bag) </k>
                  <state color="blue"> .Map </state>
          <condition color="red"> true </condition>
                </T>

/*@ The concrete semantics of IMP which remains unchanged for symbolic execution */
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
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
//  rule if (true)  S else _ => S
//  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm

//@ IMP symbolic semantics
  rule <k> I1:Int / I2:Int => I1 divInt I2 ...</k>
       <condition> Phi:Bool => Phi andBool I2 =/=Int 0 </condition>
       when checkSat(Phi andBool (I2 =/=Int 0)) =/=K "unsat" [transition]

  rule <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Bool => Phi andBool B1 ==Bool true </condition>
       when checkSat(Phi andBool B1) =/=K "unsat" [transition]

  rule <k> B1:Bool && B2:BExp => false ...</k>
       <condition> Phi:Bool => Phi andBool notBool B1 </condition>
       when checkSat(Phi andBool notBool B1) =/=K "unsat" [transition]

  rule <k> if (B:Bool) S else _ => S ...</k>
       <condition> Phi:Bool => Phi andBool B </condition>
       when checkSat(Phi andBool B) =/=K "unsat" [transition]

  rule <k> if (B:Bool) _ else S => S ...</k>
       <condition> Phi:Bool => Phi andBool notBool B </condition>
       when checkSat(Phi andBool notBool B) =/=K "unsat" [transition]

/*@ Assert semantics: remain stuck when the assertion doesn' hold. */
  rule <k> assert(B:Bool); => . ...</k>
       <condition> Phi:Bool </condition>
       when checkSat(Phi andBool B) ==K "sat"

//@ Load PGM.
   rule (<k> #ps(B:Bag) </k>
        <state> _ </state>
        <condition> _ </condition>)
    => B [structural]

endmodule
