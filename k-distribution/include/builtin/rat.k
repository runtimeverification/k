module RAT-SYNTAX
  imports INT-SYNTAX
  imports BOOL

  syntax Rat

  syntax Rat ::= Int

  syntax Rat ::= left:
                 Rat "^Rat" Int [function, functional, klabel(_^Rat_), symbol, left, smtlib(ratpow), hook(RAT.pow)]
               > left:
                 Rat "*Rat" Rat [function, functional, klabel(_*Rat_), symbol, left, smtlib(ratmul), hook(RAT.mul)]
               | Rat "/Rat" Rat [function,             klabel(_/Rat_), symbol, left, smtlib(ratdiv), hook(RAT.div)]
               > left:
                 Rat "+Rat" Rat [function, functional, klabel(_+Rat_), symbol, left, smtlib(ratadd), hook(RAT.add)]
               | Rat "-Rat" Rat [function, functional, klabel(_-Rat_), symbol, left, smtlib(ratsub), hook(RAT.sub)]

  syntax Bool ::= Rat  "==Rat" Rat [function, functional, klabel(_==Rat_),  symbol, smtlib(rateq), hook(RAT.eq)]
                | Rat "=/=Rat" Rat [function, functional, klabel(_=/=Rat_), symbol, smtlib(ratne), hook(RAT.ne)]
                | Rat   ">Rat" Rat [function, functional, klabel(_>Rat_),   symbol, smtlib(ratgt), hook(RAT.gt)]
                | Rat  ">=Rat" Rat [function, functional, klabel(_>=Rat_),  symbol, smtlib(ratge), hook(RAT.ge)]
                | Rat   "<Rat" Rat [function, functional, klabel(_<Rat_),   symbol, smtlib(ratlt), hook(RAT.lt)]
                | Rat  "<=Rat" Rat [function, functional, klabel(_<=Rat_),  symbol, smtlib(ratle), hook(RAT.le)]

  syntax Rat ::= minRat(Rat, Rat) [function, functional, klabel(minRat), symbol, smtlib(ratmin), hook(RAT.min)]
               | maxRat(Rat, Rat) [function, functional, klabel(maxRat), symbol, smtlib(ratmax), hook(RAT.max)]
endmodule

module RAT-COMMON
  imports RAT-SYNTAX

  // invariant of < I , J >Rat : I =/= 0, J >= 2, and I and J are coprime
  syntax Rat ::= "<" Int "," Int ">Rat" [format(%2 /Rat %4)]
endmodule

module RAT-SYMBOLIC [symbolic, kore]
  imports RAT-COMMON
  imports ML-SYNTAX

  rule
    #Ceil(@R1:Rat /Rat @R2:Rat)
  =>
    {(@R2 =/=Rat 0) #Equals true} #And #Ceil(@R1) #And #Ceil(@R2)
  [anywhere]
endmodule

module RAT-KORE [kore]
  imports RAT-COMMON
  imports K-EQUAL

  /*
   * equalities
   */

  // NOTE: the two rules below may not work correctly in non-kore backends

  rule R ==Rat S => R ==K S

  rule R =/=Rat S => R =/=K S
endmodule

module RAT-KAST [kast]
  imports RAT-COMMON
  imports INT

  /*
   * equalities for non-kore backends such as the java backend
   */

  rule < I , I' >Rat ==Rat < J , J' >Rat => I ==Int J andBool I' ==Int J'
  rule _:Int         ==Rat < _ , _  >Rat => false
  rule < _ , _  >Rat ==Rat _:Int         => false
  rule I:Int         ==Rat J:Int         => I ==Int J

  rule R =/=Rat S => notBool (R ==Rat S)
endmodule

module RAT
  imports RAT-COMMON
  imports RAT-SYMBOLIC
  imports RAT-KORE
  imports RAT-KAST
  imports INT

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
  syntax Int ::= gcdInt(Int, Int) [function]

  rule gcdInt(A, 0) => A        requires A >Int 0
  rule gcdInt(A, 0) => 0 -Int A requires A <Int 0
  rule gcdInt(A, B) => gcdInt(B, A %Int B) requires B =/=Int 0 // since |A %Int B| = |A| %Int |B|

  /*
   * exponentiation
   */

  rule X ^Rat 0 => 1
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

endmodule
