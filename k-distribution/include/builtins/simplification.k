// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "int.k"
require "symbolic-k.k"
/*
  Transforms a boolean formula into its disjunctive normal form.
  Each binary operation _andBool_ , _orBool_, notBool_, and _impliesBool_
  is replaced by a corresponding label which can have a variable number of arguments:
  '#andBool, '#orBool, '#notBool (_impliesBool_ is translated using '#notBool and '#orBool).
  Once the transformation is done then distributivity, negation, and De Morgan's laws are
  applied until we reach DNF.
*/
module DNF
  imports BOOL-HOOKS
  imports INT-HOOKS

  // New labels - '#andBool is already declared in K
  syntax KLabel ::= "'#notBool"
  syntax KLabel ::= "'#orBool" [predicate]

  // transforms a boolean term into the equivalent DNF one
  syntax K ::= dnf(Bool) [function]

  // literals are DNF
  rule dnf(B:Bool) => B when isLiteral(B) [anywhere]

  // implications are transformed using "'#notBool" and "'#orBool" inside each possible term
  rule dnf(B1:Bool impliesBool B2:Bool) => '#orBool('#notBool(B1),,B2) [anywhere, simplification]
  rule '#andBool(_:KList,, ((B1:Bool impliesBool B2:Bool) =>  '#orBool('#notBool(B1),,B2)) ,, _:KList ) [anywhere,simplification]
  rule '#orBool(_:KList,, ((B1:Bool impliesBool B2:Bool) =>  '#orBool('#notBool(B1),,B2)) ,, _:KList ) [anywhere, simplification]
  rule '#notBool(((B1:Bool impliesBool B2:Bool) =>  '#orBool('#notBool(B1),,B2))) [anywhere, simplification]

  // De Morgan for andBool
  rule dnf(notBool(B1:Bool andBool B2:Bool)) => '#orBool('#notBool(B1) ,, '#notBool(B2)) [anywhere, simplification]
  rule '#andBool(_:KList,, ((notBool(B1:Bool andBool B2:Bool)) => '#orBool('#notBool(B1) ,, '#notBool(B2))) ,, _:KList ) [anywhere, simplification]
  rule '#andBool(((notBool(B1:Bool andBool B2:Bool)) => '#orBool('#notBool(B1) ,, '#notBool(B2))) ,, _:KList ) [anywhere, simplification]
  rule '#orBool(_:KList,, ((notBool(B1:Bool andBool B2:Bool)) => '#orBool('#notBool(B1) ,, '#notBool(B2))) ,, _:KList ) [anywhere, simplification]

  // De Morgan for orBool
  rule dnf(notBool(B1:Bool orBool B2:Bool)) => '#andBool('#notBool(B1) ,, '#notBool(B2)) [anywhere, simplification]
  rule '#andBool(_:KList,, ((notBool(B1:Bool orBool B2:Bool)) => '#andBool('#notBool(B1) ,, '#notBool(B2))) ,, _:KList ) [anywhere, simplification]
  rule '#orBool(_:KList,, ((notBool(B1:Bool orBool B2:Bool)) => '#andBool('#notBool(B1) ,, '#notBool(B2))) ,, _:KList ) [anywhere, simplification]

  // distributivity right
  rule dnf((B1:Bool orBool B2:Bool) andBool B3:Bool) => '#orBool('#andBool(B1,,B3) ,, '#andBool(B2,,B3)) [anywhere, simplification]
  rule '#andBool(_:KList,, (((B1:Bool orBool B2:Bool) andBool B3:Bool) =>  '#orBool('#andBool(B1,,B3) ,, '#andBool(B2,,B3))) ,, _:KList ) [anywhere, simplification]
  rule '#orBool(_:KList,, (((B1:Bool orBool B2:Bool) andBool B3:Bool) =>  '#orBool('#andBool(B1,,B3) ,, '#andBool(B2,,B3))) ,, _:KList ) [anywhere, simplification]

  // distributivity left
  rule dnf(B3:Bool andBool (B1:Bool orBool B2:Bool)) => '#orBool('#andBool(B1,,B3) ,, '#andBool(B2,,B3)) [anywhere, simplification]
  rule '#andBool(_:KList,, ((B3:Bool andBool (B1:Bool orBool B2:Bool)) =>  '#orBool('#andBool(B1,,B3) ,, '#andBool(B2,,B3))) ,, _:KList ) [anywhere, simplification]
  rule '#orBool(_:KList,, ((B3:Bool andBool (B1:Bool orBool B2:Bool)) =>  '#orBool('#andBool(B1,,B3) ,, '#andBool(B2,,B3))) ,, _:KList ) [anywhere, simplification]

  // distributivity over klabels
  rule '#orBool(KL:KList) andBool B:Bool => '#orBool(distrAnd(B,KL)) [anywhere]
  rule B:Bool andBool '#orBool(KL:KList) => '#orBool(distrAnd(B,KL)) [anywhere]
  rule '#andBool(KL1:KList,, '#orBool(KL2:KList)) => '#orBool(distrAnd(KL1,KL2)) [anywhere]
  rule '#andBool('#orBool(KL2:KList),, KL1:KList) => '#orBool(distrAnd(KL1,KL2)) [anywhere]

  // conjuction simplification inside terms
  rule dnf(B1:Bool andBool B2:Bool) => '#andBool(B1,,B2) [anywhere, simplification]
  rule '#andBool(_:KList,, ((B1:Bool andBool B2:Bool) => '#andBool(B1,,B2)) ,, _:KList) [anywhere, simplification]
  rule '#orBool(_:KList,, ((B1:Bool andBool B2:Bool) => '#andBool(B1,,B2)) ,, _:KList) [anywhere, simplification]

  // disjunction simplification inside terms
  rule dnf(B1:Bool orBool B2:Bool) => '#orBool(B1,,B2) [anywhere, simplification]
  rule '#andBool(_:KList,, ((B1:Bool orBool B2:Bool) => '#orBool(B1,,B2)) ,, _:KList) [anywhere, simplification]
  rule '#orBool(_:KList,, ((B1:Bool orBool B2:Bool) => '#orBool(B1,,B2)) ,, _:KList) [anywhere, simplification]

  // negations
  rule notBool('#andBool(KL:KList)) => '#orBool('#notBool(KL),,.KList) [anywhere, simplification]
  rule notBool('#orBool(KL:KList))  => '#andBool('#notBool(KL),,.KList) [anywhere, simplification]


  // negation
  rule notBool('#notBool(B:Bool)) => B [anywhere, simplification]
  rule '#notBool(notBool(B:Bool)) => B [anywhere, simplification]

//  collapse andBool
  rule '#andBool(_,, ((B1:Bool andBool B2:Bool) => (B1 ,, B2)) ,, _) [anywhere, simplification]
  rule '#andBool(_,, ('#andBool(KL:KList) => KL),, _ ) [anywhere]
  rule isBool('#andBool(_:KList)) => true

  // collapse orBool
  rule '#orBool(_,, ((B1:Bool orBool B2:Bool) => (B1 ,, B2)) ,, _) [anywhere, simplification]
  rule '#orBool(_,, ('#orBool(KL:KList) => KL),, _ ) [anywhere]
  rule isBool('#orBool(_:KList)) => true


  // Distribute notBool
  rule '#notBool(B:Bool,,Rest:KList) => notBool(B),,'#notBool(Rest) [anywhere]
  rule '#notBool(.KList) => .KList [anywhere]

  // apply distributivity: List x List and Element x List
  syntax KList ::= distrAnd(KList,KList) [function]
               | distrAndBool(Bool, KList) [function]
  rule distrAnd((B:Bool,,Rest:KList), KL:KList) => (distrAndBool(B, KL),,distrAnd(Rest, KL))
  rule distrAnd(.KList, _) => .KList
  rule distrAndBool(B:Bool, B':Bool,,KL:KList) => '#andBool(B,,B'),,distrAndBool(B, KL)
  rule distrAndBool(_:Bool, .KList) => .KList

  // returns true when the argument is a boolean literal
  // (irreducible boolean term)
  syntax Bool ::= isLiteral(Bool) [function]
  rule isLiteral(notBool B:Bool) => true when isLiteral(B) [simplification]
  rule isLiteral(#symBool(K)) => true
  rule isLiteral(B:#Bool) => true
  rule isLiteral(I1:Int ==Int I2:Int) => true
  rule isLiteral(I1:Int <=Int I2:Int) => true
  rule isLiteral(I1:Int  <Int I2:Int) => true
  rule isLiteral(I1:Int >=Int I2:Int) => true
  rule isLiteral(I1:Int  >Int I2:Int) => true

endmodule

/*
  Simplification module for boolean formulas.
  It includes the DNF modules and separate modules
  corresponding to functions specifications.
*/
module SIMPLIFICATION
  imports DNF
  imports PROOF-BASIC
  imports GCD
  imports SYMBOLIC-K

  // Do not attach sorts to these variables other than K
  rule '#andBool(_,, B:Bool,, _ ,, (B => .KList) ,, _ ) [anywhere]
  rule '#andBool(_,, B,, _ ,, B' ,, _ ) => false when B |- (notBool B') [anywhere]
  rule '#orBool(_,,B,, _ ) => true when B [anywhere]

  // these rule make sense for symbolic boolean expressions
  rule B ==Bool true => B [simplification, anywhere]
  rule true ==Bool B => B [simplification, anywhere]
  rule B ==Bool false => notBool B [simplification, anywhere]
  rule false ==Bool B => notBool B [simplification, anywhere]
  rule notBool(notBool(B:Bool)) => B [anywhere, simplification]

  // unflat: transforms labels for boolean operations: '#andBool,
  // '#orBool, '#notBool into corresponding binary operations
  // andBool, orBool, notBool
  syntax Bool ::= unflat(K) [function]

  rule unflat('#orBool(B,,Rest)) => unflat(B) orBool unflat('#orBool(Rest)) [anywhere]
  rule unflat('#orBool(.KList)) => false [anywhere]
  rule unflat('#andBool(B,,Rest)) => unflat(B) andBool unflat('#andBool(Rest)) [anywhere]
  rule unflat('#andBool(.KList)) => true [anywhere]
  rule unflat('#notBool(B)) => notBool unflat(B) [anywhere]
  rule unflat(B:Bool) => B when isLiteral(B) [anywhere]

  rule unflat(forall S . B) => forall S . unflat(B) [anywhere]
  rule unflat(exists S . B) => exists S . unflat(B) [anywhere]

  rule unflat(B orBool B') => unflat(B) orBool unflat(B') [anywhere]
  rule unflat(B andBool B') => unflat(B) orBool unflat(B') [anywhere]
  rule unflat(notBool B) => notBool unflat(B) [anywhere]
  rule unflat(B impliesBool B') => unflat(B) impliesBool unflat(B') [anywhere]

endmodule

/*
  Deduction relation module and its main rules.
*/
module PROOF-BASIC
  imports BOOL-HOOKS

  // deduction relation syntax
  syntax Bool ::= Bool "|-" Bool [function]

  // Each component of a disjunction can be deduce
  rule '#andBool(_,,B,,_) |- B => true

  // B /\ not B makes the conjunction false
  rule '#andBool(B1,,B,,B2) => false
      when '#andBool(B1,,B2) |- (notBool B)

endmodule

/*
  Specification of GCD (greatest common divisor) function
*/
module GCD
  imports BOOL-HOOKS
  imports INT-HOOKS
  imports PROOF-BASIC

  // gcd function syntax
  syntax Int ::= "gcd" "(" Int "," Int ")" [function, smtlib(gcd)]

  // gcd(A,B) = gcd(X, Y) /\ Y > 0  |-  gcd(X, X%Y)
  rule '#andBool(B1,, gcd(A:Int, B:Int) ==Int gcd(X:Int, Y:Int),, B2)
       |- (gcd(A:Int, B:Int) ==Int gcd(Y:Int, X modInt Y)) => true
       when '#andBool(B1,,B2) |- (Y >Int 0) [anywhere, simplification]

  // gcd(A,B) = gcd(X,Y) /\ Y == 0  |-  X == gcd(A,B)
  rule '#andBool(B1,, (gcd(A:Int, B:Int) ==Int gcd(X:Int, Y:Int)),, B2)
        |- X ==Int gcd(A:Int, B:Int) => true
        when '#andBool(B1,,B2) |- (Y ==Int 0) [anywhere, simplification]

  // I == gcd(X, Y) /\ Y == 0  |-  I == X
  rule '#andBool(B1,, (I:Int ==Int gcd(X:Int, Y:Int)),, B2)
       |- I ==Int X => true
       when '#andBool(B1,,B2) |- Y ==Int 0 [anywhere, simplification]

  // not(I == gcd(X, Y) /\ Y == 0)  |-  not(I == X)
  rule '#andBool(B1,, notBool (I:Int ==Int gcd(X:Int, Y:Int)),, B2)
       |- notBool (I ==Int X) => true
       when '#andBool(B1,,B2) |- Y ==Int 0 [anywhere, simplification]

endmodule

