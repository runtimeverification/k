// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*@
This is the symbolic semantics of IMP enriched with arrays and Hoare logic.
The semantics, gets as input an IMP program, annotated with pre and post
conditions and invariants.
*/
require "symbolic-array.k"


module IMP-SYNTAX
  imports SYMBOLIC-ARRAY-SYNTAX

  syntax AExp  ::= Int | Id
                 | AExp "[" AExp "]"          [strict]
                 > left:
                   AExp "*" AExp              [left, strict]
                 | AExp "/" AExp              [left, strict]
                 > left:
                   AExp "+" AExp              [left, strict]
                 | AExp "-" AExp              [left, strict]
                 > "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | AExp "==" AExp             [strict]
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
  syntax AExps ::= List{AExp,","}
  syntax Ids   ::= List{Id,","}

  syntax Stmt ::= "while " "(" BExp ")" "invariant" ":" Assert Block
  syntax Assert ::= BExp
                  | "not" Assert                [strict]
                  | Assert "and" Assert         [left, strict]
                  > Assert "or" Assert          [left, strict]
                  > Assert "implies" Assert     [left, strict]
                  | "forall" Ids "(" Assert ")" [strict(2)]
                  | "exists" Ids "(" Assert ")" [strict(2)]

  syntax Pre   ::= "pre"  ":" Assert
  syntax Post  ::= "post" ":" Assert
  syntax Program ::= "int" AExps ";" Pre Post Stmt

  // Values
  syntax Val ::= Int | Bool | Array
               | "array" "(" Int "," Int ")"
               | "loc" "(" AExp ")"
  syntax AExp ::= Val

endmodule

module IMP
  imports IMP-SYNTAX
  imports SYMBOLIC-ARRAY

  syntax KResult ::= Val

  configuration <T color="yellow">
                  <k color="green"> $PGM:Program </k>
                  <env color="black"> .Map </env>
                  <store color="blue"> .Map </store>
                  <condition color="red"> true </condition>
                </T>

//@ IMP concrete semantics
// AExp
  rule <k> X:Id => V ...</k> <env>... X |-> L ...</env> <store>... L:Int |-> V:Val </store>
  rule <k> array(L:Int, Size:Int)[I:Int] => lookup(L +Int I) ...</k>
       <store>... L |-> _:#Int ...</store>

  rule <k> array(L:Int, Size:Int)[I:Int] => select(A, I) ...</k>
       <store>... L |-> A:Array ...</store>

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

// lvalue
  syntax AExp ::= "lvalue" "(" K ")"

// Local variable
  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

// lookup
  syntax KItem ::= "lookup" "(" Int ")"
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

// Stmt
  context (HOLE => lvalue(HOLE)) = _;
  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

  rule <k> loc(L:Int) = I:Int; => . ...</k> <store>... L |-> (_ => I) ...</store>
  rule <k> loc(array(L:Int, Size:Int)[I:Int]) = V:Val; => . ...</k>
       <store>... L |-> (A:Array => store(A, I, V)) ...</store>
  rule <k> lvalue(array(L:Int, Size:Int)[I:Int]) => loc(L +Int I) ...</k>
       <store>... L |-> _:Int ...</store>

  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X:Id,Xs:AExps => Xs); _:Pre _:Post _:Stmt </k>
       <env> Rho:Map (.Map => X |-> !L:Int) </env>
       <store>... .Map => (!L |-> 0) </store>
       when notBool (X in keys(Rho))

  // symbolic arrays
  rule <k> int (X:Id [S:#Int] ,Xs:Ids => Xs); _:Pre _:Post St:Stmt </k>
       <env> Rho:Map (.Map => X |-> !L:Int) </env>
       <store>... (.Map => !L |-> array(!AL, S) !AL |-> #symArray(X) ) </store>
       when notBool (X in keys(Rho))

  rule int .AExps ; P:Pre P':Post S:Stmt => P ~> P' ~> S [structural]

//@ IMP symbolic semantics
  rule <T> <k> I1:Int / I2:Int => I1 /Int I2 ...</k>
       <condition> Phi:Bool => Phi andBool I2 =/=Int 0 </condition> ...</T>
       when checkSat(Phi andBool (I2 =/=Int 0)) ==K "sat" [transition]

  rule <T> <k> B1:Bool && B2:BExp => B2 ...</k>
       <condition> Phi:Bool => Phi andBool B1 ==Bool true </condition> ...</T>
       when checkSat(Phi andBool B1) ==K "sat" [transition]

  rule <T> <k> B1:Bool && B2:Bool => false ...</k>
       <condition> Phi:Bool => Phi andBool notBool B1 </condition> ...</T>
       when checkSat(Phi andBool notBool B1) ==K "sat" [transition]

  rule <T> <k> if (B:Bool) S::Block else _ => S ...</k>
       <condition> Phi:Bool => Phi andBool B </condition> ...</T>
       when checkSat(Phi andBool B) ==K "sat" [transition]

  rule <T> <k> if (B:Bool) _ else S::Block => S ...</k>
       <condition> Phi:Bool => Phi andBool notBool B </condition> ...</T>
       when checkSat(Phi andBool notBool B) ==K "sat" [transition]

//@ Hoare triples
  rule <k> (pre: Psi:Assert ~> post: Psi':Assert ~> S:Stmt)
            =>
            assume(Psi) ~> S ~> match(A2M(Psi'))
       </k>

//@ Assume
  syntax KItem ::= "assume" "(" K ")"
                 | "assumeStrict" "(" K ")" [strict]

  rule assume(Psi:K) => assumeStrict(A2M(Psi))
  rule <k> assumeStrict(m2k(E:Map, Phi:K)) => . ...</k>
       <store> _ => E </store>
       <condition> _ => Phi </condition>

//@ Match
  syntax KItem ::= "match"  "(" K ")" [strict]
  rule <k> match(m2k(Ea:Map, Phia:K))
       => . // checkSat(Phic andBool (notBool Phia) andBool mapLeftEq(Ea, Ec))
       ...</k>
       <store> Ec:Map </store>
       <condition> Phic:Bool </condition>
       when checkSat(Phic andBool (notBool Phia) andBool mapLeftEq(Ea, Ec)) ==K "unsat"

// debug rule
  rule <k> match(m2k(Ea:Map, Phia:K))
       => SMTLibQuery(Phic andBool (notBool Phia) andBool mapLeftEq(Ea, Ec))
       ...</k>
       <store> Ec:Map </store>
       <condition> Phic:Bool </condition>
       when checkSat(Phic andBool (notBool Phia) andBool mapLeftEq(Ea, Ec)) ==K "sat"

//@ While invariant
  rule <k> while ( B:BExp ) invariant: Psi:Assert S:Block ~> K
           =>
           assume(Psi and B) ~> S ~> match(A2M(Psi))
       </k>
       [transition]
  rule <k> while ( B:BExp ) invariant: Psi:Assert _:Block
           => match(A2M(Psi)) ~> assume(Psi and not B)
       ...</k>
       [transition]

//@ A2M
  syntax KItem ::= "A2M" "(" K ")"
  rule <k> A2M(Psi)
           =>
           generateFresh(E) ~> evalAssert(Psi) ~> restore(E, Phi)
       ...</k>
       <store> E:Map </store>
       <condition> Phi:Bool </condition>

//@ Generate fresh map
  syntax KItem ::= "generateFresh" "(" Map ")"
  rule <k> generateFresh(L:Int |-> V:Int E:Map) => generateFresh(E) ...</k>
       <store>... L |-> (V => !V':Int) ...</store>
  rule <k> generateFresh(.Map) => . ...</k>
  rule <k> generateFresh(L:Int |-> array(AL:Int, Size:Int) E:Map) => generateFresh(E) ...</k>
  rule <k> generateFresh(L:Int |-> A:Array E:Map) => generateFresh(E) ...</k>

//@ Assert evaluation
  syntax KItem ::= "evalAssert" "(" K ")" [strict]
  syntax KResult ::= "m2k" "(" Map "," K ")"

  rule <k> evalAssert(Phi:K) ~> restore(E':Map, Phi':K)
           =>
           m2k(E, Phi)
       ...</k>
       <store> E:Map => E' </store>
       <condition> _ => Phi' </condition>

//@ Restore
  syntax KItem ::= "restore" "(" Map "," Bool ")"

//@ Assertions
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1:Bool implies B2:Bool => B1 impliesBool B2
  rule B1:Bool  or B2:Bool => B1  orBool B2
  rule not B:Bool => notBool B
  rule forall Is:Ids (B:Bool) => forall toSet(Is) . B
  rule exists Is:Ids (B:Bool) => exists toSet(Is) . B

  syntax Set ::= "toSet" "(" Ids ")" [function]
  rule toSet(.Ids) => .Set
  rule toSet(X:Id, Is:Ids) => SetItem(#symInt(X)) toSet(Is)


//@ Utils
  syntax Bool ::= "mapLeftEq" "(" Map "," Map ")" [function]
  rule mapLeftEq(X:Int |-> V1:Int Rest:Map, X |-> V2 Rest2:Map) => V1 ==Int V2 andBool mapLeftEq(Rest, Rest2)
  rule mapLeftEq(X:Int |-> array(AL:Int, Sz:Int) Rest:Map, X |-> array(AL, Sz) Rest2:Map) => mapLeftEq(Rest, Rest2)
  rule mapLeftEq(X:Int |-> A:Array Rest:Map, X |-> A Rest2:Map) => mapLeftEq(Rest, Rest2)
  rule mapLeftEq(. , _) => true
  rule mapLeftEq(X:Int |-> _:Int _:Map, Right:Map) => false when notBool(X in keys(Right))
  rule mapLeftEq(M:Map, .) => false when notBool(keys(M) ==K .Set)

//@ Compiler issues
  // subsort issue?
  rule isSymbolicInt(select(A:Array, I:Int)) => true [anywhere]
  rule isInt(select(A:Array, I:Int)) => true [anywhere]
// contexts limitation: array(I,S)[V] must be a KResult to cool lvalue(array(I,S)[V])
  rule lvalue(array(I:Int, S:Int)[V:Int]) => lvalue(loc(array(I:Int, S:Int)[V:Int]))
  rule K2Sort(_:Array) => "(Array Int Int)" // support only integer arrays

// forall binders
  rule <k> X:Id => #symInt(X) ...</k>
       <env> Rho </env>
       when notBool(X in keys(Rho))
endmodule
