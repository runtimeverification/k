---
copyright: Copyright (c) 2019-2020 K Team. All Rights Reserverd.
---

Rational Numbers in K
=====================

K provides support for arbitrary-precision rational numbers represented as a 
quotient between two integers. The sort representing these values is `Rat`.
`Int` is a subsort of `Rat`, and it is guaranteed that any integer will be
represented as an `Int` and can be matched as such on the left hand side
of rules. K also supports the usual arithmetic operators over rational numbers.

```k
module RAT-SYNTAX
  imports INT-SYNTAX
  imports private BOOL

  syntax Rat

  syntax Rat ::= Int
```

Arithmetic
----------

You can:

* Raise a rational number to any negative or nonnegative integer.
* Multiply or divide two rational numbers to obtain a product or quotient.
* Add or subtract two rational numbers to obtain a sum or difference.

```k
  syntax Rat ::= left:
                 Rat "^Rat" Int [function, functional, klabel(_^Rat_), symbol, left, smtlib(ratpow), hook(RAT.pow)]
               > left:
                 Rat "*Rat" Rat [function, functional, klabel(_*Rat_), symbol, left, smtlib(ratmul), hook(RAT.mul)]
               | Rat "/Rat" Rat [function,             klabel(_/Rat_), symbol, left, smtlib(ratdiv), hook(RAT.div)]
               > left:
                 Rat "+Rat" Rat [function, functional, klabel(_+Rat_), symbol, left, smtlib(ratadd), hook(RAT.add)]
               | Rat "-Rat" Rat [function, functional, klabel(_-Rat_), symbol, left, smtlib(ratsub), hook(RAT.sub)]
```

Comparison
----------

You can determine whether two rational numbers are equal, unequal, or compare
one of less than, less than or equalto, greater than, or greater than or equal
to the other:

```k
  syntax Bool ::= Rat  "==Rat" Rat [function, functional, klabel(_==Rat_),  symbol, smtlib(rateq), hook(RAT.eq)]
                | Rat "=/=Rat" Rat [function, functional, klabel(_=/=Rat_), symbol, smtlib(ratne), hook(RAT.ne)]
                | Rat   ">Rat" Rat [function, functional, klabel(_>Rat_),   symbol, smtlib(ratgt), hook(RAT.gt)]
                | Rat  ">=Rat" Rat [function, functional, klabel(_>=Rat_),  symbol, smtlib(ratge), hook(RAT.ge)]
                | Rat   "<Rat" Rat [function, functional, klabel(_<Rat_),   symbol, smtlib(ratlt), hook(RAT.lt)]
                | Rat  "<=Rat" Rat [function, functional, klabel(_<=Rat_),  symbol, smtlib(ratle), hook(RAT.le)]
```

Min/Max
-------

You can compute the minimum and maximum of two rational numbers:

```k
  syntax Rat ::= minRat(Rat, Rat) [function, functional, klabel(minRat), symbol, smtlib(ratmin), hook(RAT.min)]
               | maxRat(Rat, Rat) [function, functional, klabel(maxRat), symbol, smtlib(ratmax), hook(RAT.max)]
```

Conversion to Floating Point
----------------------------

You can convert a rational number to the nearest floating point number that
is representable in a `Float` of a specified number of precision and exponent
bits:

```k
  syntax Float ::= Rat2Float(Rat, precision: Int, exponentBits: Int) [function]
endmodule
```

Implementation of Rational Numbers
----------------------------------

The remainder of this file consists of an implementation in K of the
operations listed above. Users of the RAT module should not use any of the
syntax defined in any of these modules.

As a point of reference for users, it is worth noting that rational numbers
are normalized to a canonical form by this module,. with the canonical form
bearing the property that it is either an `Int`, or a pair of integers
`I /Rat J` such that
`I =/=Int 0 andBool J >=Int 2 andBool gcdInt(I, J) ==Int 1` is always true.

```k
module RAT-COMMON
  imports RAT-SYNTAX

  // invariant of < I , J >Rat : I =/= 0, J >= 2, and I and J are coprime
  syntax Rat ::= "<" Int "," Int ">Rat" [format(%2 /Rat %4)]
endmodule

module RAT-SYMBOLIC [symbolic, kore]
  imports private RAT-COMMON
  imports ML-SYNTAX
  imports private BOOL

  rule
    #Ceil(@R1:Rat /Rat @R2:Rat)
  =>
    {(@R2 =/=Rat 0) #Equals true} #And #Ceil(@R1) #And #Ceil(@R2)
  [simplification, anywhere]
endmodule

module RAT-KORE [kore]
  imports private RAT-COMMON
  imports private K-EQUAL

  /*
   * equalities
   */

  // NOTE: the two rules below may not work correctly in non-kore backends

  rule R ==Rat S => R ==K S

  rule R =/=Rat S => R =/=K S
endmodule

module RAT-KAST [kast]
  imports private RAT-COMMON
  imports private INT
  imports private BOOL

  /*
   * equalities for non-kore backends such as the java backend
   */

  rule < I , I' >Rat ==Rat < J , J' >Rat => I ==Int J andBool I' ==Int J'
  rule _:Int         ==Rat < _ , _  >Rat => false
  rule < _ , _  >Rat ==Rat _:Int         => false
  rule I:Int         ==Rat J:Int         => I ==Int J

  rule R =/=Rat S => notBool (R ==Rat S)
endmodule

module RAT [private]
  imports private RAT-COMMON
  imports RAT-SYMBOLIC
  imports RAT-KORE
  imports RAT-KAST
  imports RAT-SYNTAX
  imports private INT
  imports private BOOL

  /*
   * arithmetic
   */

  rule < I , I' >Rat +Rat < J , J' >Rat => ((I *Int J') +Int (I' *Int J)) /Rat (I' *Int J')
  rule I:Int         +Rat < J , J' >Rat => ((I *Int J') +Int J) /Rat J'
  rule < J , J' >Rat +Rat I:Int         => I +Rat < J , J' >Rat
  rule I:Int         +Rat J:Int         => I +Int J

  rule < I , I' >Rat *Rat < J , J' >Rat => (I *Int J) /Rat (I' *Int J')
  rule I:Int         *Rat < J , J' >Rat => (I *Int J) /Rat J'
  rule < J , J' >Rat *Rat I:Int         => I *Rat < J , J' >Rat
  rule I:Int         *Rat J:Int         => I *Int J

  rule < I , I' >Rat /Rat < J , J' >Rat => (I *Int J') /Rat (I' *Int J)
  rule I:Int         /Rat < J , J' >Rat => (I *Int J') /Rat J
  rule < I , I' >Rat /Rat J:Int         => I /Rat (I' *Int J) requires J =/=Int 0
  rule I:Int         /Rat J:Int         => makeRat(I, J)      requires J =/=Int 0

  // derived

  rule R -Rat S => R +Rat (-1 *Rat S)

  // normalize

  syntax Rat ::= makeRat(Int, Int)      [function]
               | makeRat(Int, Int, Int) [function]

  rule makeRat(0, J) => 0 requires J =/=Int 0

  rule makeRat(I, J) => makeRat(I, J, gcdInt(I,J)) requires I =/=Int 0 andBool J =/=Int 0

  // makeRat(I, J, D) is defined when I =/= 0, J =/= 0, D > 0, and D = gcd(I,J)
  rule makeRat(I, J, D) => I /Int D                       requires J ==Int D // implies J > 0 since D > 0
  rule makeRat(I, J, D) => < I /Int D , J /Int D >Rat     requires J >Int 0 andBool J =/=Int D
  rule makeRat(I, J, D) => makeRat(0 -Int I, 0 -Int J, D) requires J <Int 0

  // gcdInt(a,b) computes the gcd of |a| and |b|, which is positive.
  syntax Int ::= gcdInt(Int, Int) [function, public]

  rule gcdInt(A, 0) => A        requires A >Int 0
  rule gcdInt(A, 0) => 0 -Int A requires A <Int 0
  rule gcdInt(A, B) => gcdInt(B, A %Int B) requires B =/=Int 0 // since |A %Int B| = |A| %Int |B|

  /*
   * exponentiation
   */

  rule _ ^Rat 0 => 1
  rule 0 ^Rat N => 0 requires N =/=Int 0

  rule < I , J >Rat ^Rat N => powRat(< I , J >Rat, N) requires N >Int 0
  rule X:Int        ^Rat N => X ^Int N                requires N >Int 0

  rule X ^Rat N => (1 /Rat X) ^Rat (0 -Int N) requires X =/=Rat 0 andBool N <Int 0

  // exponentiation by squaring

  syntax Rat ::= powRat(Rat, Int) [function]

  // powRat(X, N) is defined when X =/= 0 and N > 0
  rule powRat(X, 1) => X
  rule powRat(X, N) => powRat(X *Rat X, N /Int 2) requires N >Int 1 andBool N %Int 2  ==Int 0
  rule powRat(X, N) => powRat(X, N -Int 1) *Rat X requires N >Int 1 andBool N %Int 2 =/=Int 0

  /*
   * inequalities
   */

  rule R >Rat S => R -Rat S >Rat 0 requires S =/=Rat 0

  rule < I , _ >Rat >Rat 0 => I >Int 0
  rule I:Int        >Rat 0 => I >Int 0

  // derived

  rule R >=Rat S => notBool R <Rat S

  rule R <Rat S => S >Rat R

  rule R <=Rat S => S >=Rat R

  rule minRat(R, S) => R requires R <=Rat S
  rule minRat(R, S) => S requires S <=Rat R

  rule maxRat(R, S) => R requires R >=Rat S
  rule maxRat(R, S) => S requires S >=Rat R

  syntax Float ::= #Rat2Float(Int, Int, Int, Int) [function, hook(FLOAT.rat2float)]
  rule Rat2Float(Num:Int, Prec:Int, Exp:Int) => #Rat2Float(Num, 1, Prec, Exp)
  rule Rat2Float(< Num, Dem >Rat, Prec, Exp) => #Rat2Float(Num, Dem, Prec, Exp)

endmodule
```
