module RAT-SYNTAX
  imports INT-SYNTAX
  imports BOOL

  syntax Rat

  syntax Rat ::= Int

  syntax Rat ::= left:
                 Rat "*Rat" Rat [function, functional, klabel(_*Rat_), symbol, left, smtlib(ratmul), hook(RAT.mul)]
               | Rat "/Rat" Rat [function,             klabel(_/Rat_), symbol, left, smtlib(ratdiv), hook(RAT.div)]
               > left:
                 Rat "+Rat" Rat [function, functional, klabel(_+Rat_), symbol, left, smtlib(ratadd), hook(RAT.add)]
               | Rat "-Rat" Rat [function, functional, klabel(_-Rat_), symbol, left, smtlib(ratsub), hook(RAT.sub)]

  syntax Rat ::= "(" Rat ")" [bracket]

  syntax Bool ::= Rat  "==Rat" Rat [function, functional, klabel(_==Rat_),  symbol, left, smtlib(rateq), hook(RAT.eq)]
                | Rat "=/=Rat" Rat [function, functional, klabel(_=/=Rat_), symbol, left, smtlib(ratne), hook(RAT.ne)]
                | Rat   ">Rat" Rat [function, functional, klabel(_>Rat_),   symbol, left, smtlib(ratgt), hook(RAT.gt)]
                | Rat  ">=Rat" Rat [function, functional, klabel(_>=Rat_),  symbol, left, smtlib(ratge), hook(RAT.ge)]
                | Rat   "<Rat" Rat [function, functional, klabel(_<Rat_),   symbol, left, smtlib(ratlt), hook(RAT.lt)]
                | Rat  "<=Rat" Rat [function, functional, klabel(_<=Rat_),  symbol, left, smtlib(ratle), hook(RAT.le)]
endmodule

module RAT-SYMBOLIC [symbolic, kore]
  imports RAT-SYNTAX
  imports ML-SYNTAX

  rule
    #Ceil(@R1:Rat /Rat @R2:Rat)
  =>
    {(@R2 =/=Rat 0) #Equals true} #And #Ceil(@R1) #And #Ceil(@R2)
  [anywhere]
endmodule

module RAT
  imports RAT-SYNTAX
  imports RAT-SYMBOLIC
  imports INT

  syntax Rat ::= "<" Int "," Int ">Rat" [format(%2 /Rat %4)]

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

  rule makeRat(I, 1, _) => I
  rule makeRat(I, J, D) => < I /Int D , J /Int D >Rat     requires J >Int 1
  rule makeRat(I, J, D) => makeRat(0 -Int I, 0 -Int J, D) requires J <Int 0

  // gcdInt(a,b) computes the gcd of |a| and |b|, which is positive.
  syntax Int ::= gcdInt(Int, Int) [function]

  rule gcdInt(A, 0) => A        requires A >Int 0
  rule gcdInt(A, 0) => 0 -Int A requires A <Int 0
  rule gcdInt(A, B) => gcdInt(B, A %Int B) requires B =/=Int 0 // since |A %Int B| = |A| %Int |B|

  /*
   * equalities
   */

  // NOTE: the two rules below may not work correctly in the java backend

  rule R ==Rat S => R ==K S

  rule R =/=Rat S => R =/=K S

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

endmodule
