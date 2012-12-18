require "int.k"
require "k-equal.k"


module MINT
  imports INT-HOOKS
  imports K-EQUAL-HOOKS

  /* Machine integer of bitwidth, interpreted value */
  syntax MInt ::= "mi" "(" Nat "," Int ")"

  syntax Int ::= "wMInt" "(" MInt ")"   [function]
               | "iMInt" "(" MInt ")"   [function]
  rule wMInt(mi(N:Nat, _)) => N 
  rule iMInt(mi(_, I:Int)) => I 

  syntax Int ::= "infMInt" "(" Nat ")"    [function]
               | "supMInt" "(" Nat ")"    [function]
               | "uinfMInt" "(" Nat ")"   [function]
               | "usupMInt" "(" Nat ")"   [function]
  rule infMInt(N:Nat) => 0 -Int (1 <<Int (N -Int 1))
  rule supMInt(N:Nat) => (1 <<Int (N -Int 1)) -Int 1
  rule uinfMInt(N:Nat) => 0 
  rule usupMInt(N:Nat) => (1 <<Int N) -Int 1
 
  /* Functions for signed and unsigned interpretations of machine integers. */
  syntax MInt ::= "sMInt" "(" MInt ")"        [function]
                | "uMInt" "(" MInt ")"        [function]
  rule uMInt(mi(N:Nat, I:Int)) => mi(N, (I modInt (1 <<Int N)))
  rule
    sMInt(mi(N:Nat, I:Int))
  =>
    mi(N,
       ((I +Int (1 <<Int (N -Int 1))) modInt (1 <<Int N))
         -Int (1 <<Int (N -Int 1)))

  /* Machine integer operations results */
  syntax MIntRes ::= "resMInt" "(" MInt "," Bool "," Bool ")"
                   | "errMInt"

  syntax MInt ::= "miMInt" "(" MIntRes ")"    [function]
  rule miMInt(resMInt(MI:MInt, _, _)) => MI

  /* NOTE: what is the difference between predicate and function? */
  syntax Bool ::= "ofMInt" "(" MIntRes")"   [function]
                | "ufMInt" "(" MIntRes")"   [function]
  rule ufMInt(resMInt(_, B:Bool, _)) => B
  rule ofMInt(resMInt(_, _, B:Bool)) => B


  /* 
   * Arithmetic operations.
   *   op   interprets the operands as signed 
   *   uop  interprets the operands as unsigned
   */
  syntax MIntRes ::= "addMInt" "(" MInt "," MInt ")"    [function]
                   | "uaddMInt" "(" MInt "," MInt ")"   [function]
                   | "subMInt" "(" MInt "," MInt ")"    [function]
                   | "usubMInt" "(" MInt "," MInt ")"   [function]
                   | "mulMInt" "(" MInt "," MInt ")"    [function]
                   | "umulMInt" "(" MInt "," MInt ")"   [function]
                   | "divMInt" "(" MInt "," MInt ")"    [function]
                   | "udivMInt" "(" MInt "," MInt ")"   [function]
                   | "remMInt" "(" MInt "," MInt ")"    [function]
                   | "uremMInt" "(" MInt "," MInt ")"   [function]

  /* Bitwise operations */
  syntax MIntRes ::= "shlMInt" "(" MInt "," Nat ")"     [function]
                   | "ushlMInt" "(" MInt "," Nat ")"    [function]
                   | "shrMInt" "(" MInt "," Nat ")"     [function]
                   | "ushrMInt" "(" MInt "," Nat ")"    [function]
                   | "andMInt" "(" MInt "," MInt ")"    [function]
                   | "xorMInt" "(" MInt "," MInt ")"    [function]
                   | "orMInt" "(" MInt "," MInt ")"     [function]
                   | "negMInt" "(" MInt ")"             [function]

  /* */
  syntax MIntRes ::= "minMInt" "(" MInt "," MInt ")"    [function]
                   | "maxMInt" "(" MInt "," MInt ")"    [function]
                   | "absMInt" "(" MInt ")"             [function]

  syntax Bool ::= "ltMInt" "(" MInt "," MInt ")"      [function]
                | "ultMInt" "(" MInt "," MInt ")"     [function]
                | "leqMInt" "(" MInt "," MInt ")"     [function]
                | "uleqMInt" "(" MInt "," MInt ")"    [function]
                | "gtMInt" "(" MInt "," MInt ")"      [function]
                | "ugtMInt" "(" MInt "," MInt ")"     [function]
                | "geqMInt" "(" MInt "," MInt ")"     [function]
                | "ugeqMInt" "(" MInt "," MInt ")"    [function]
                | MInt "==MInt" MInt                  [function]
                | MInt "=/=MInt" MInt                 [function]

  /*
   * Arithmetic operations
   */
  rule
    addMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(
        sMInt(mi(N, I1 +Int I2)),
        iMInt(sMInt(mi(N, I1))) +Int iMInt(sMInt(mi(N, I2))) <Int infMInt(N),
        iMInt(sMInt(mi(N, I1))) +Int iMInt(sMInt(mi(N, I2))) >Int supMInt(N))
  rule
    uaddMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(
        uMInt(mi(N, I1 +Int I2)),
        false,
        iMInt(uMInt(mi(N, I1))) +Int iMInt(uMInt(mi(N, I2))) >Int usupMInt(N))

  rule
    subMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(
        sMInt(mi(N, I1 -Int I2)),
        iMInt(sMInt(mi(N, I1))) -Int iMInt(sMInt(mi(N, I2))) <Int infMInt(N),
        iMInt(sMInt(mi(N, I1))) -Int iMInt(sMInt(mi(N, I2))) >Int supMInt(N))
  rule
    usubMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(
        uMInt(mi(N, I1 -Int I2)),
        iMInt(uMInt(mi(N, I1))) -Int iMInt(uMInt(mi(N, I2))) <Int uinfMInt(N),
        false)

  rule
    mulMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(
        sMInt(mi(N, I1 *Int I2)),
        iMInt(sMInt(mi(N, I1))) *Int iMInt(sMInt(mi(N, I2))) <Int infMInt(N),
        iMInt(sMInt(mi(N, I1))) *Int iMInt(sMInt(mi(N, I2))) >Int supMInt(N))
  rule
    umulMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(
        uMInt(mi(N, I1 *Int I2)),
        false,
        iMInt(uMInt(mi(N, I1))) *Int iMInt(uMInt(mi(N, I2))) >Int usupMInt(N))

  rule
    divMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    #if iMInt(sMInt(mi(N, I2))) =/=Int 0 #then
      resMInt(
          sMInt(mi(N, iMInt(sMInt(mi(N, I1))) /Int iMInt(sMInt(mi(N, I2))))),
          false,
          iMInt(sMInt(mi(N, I1))) /Int iMInt(sMInt(mi(N, I2))) >Int supMInt(N))
    #else
      errMInt
    #fi
  rule
    udivMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    #if iMInt(uMInt(mi(N, I2))) =/=Int 0 #then
      resMInt(
          mi(N, iMInt(uMInt(mi(N, I1))) /Int iMInt(uMInt(mi(N, I2)))),
          false,
          false)
    #else
      errMInt
    #fi

  rule
    remMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    #if iMInt(sMInt(mi(N, I2))) =/=Int 0 #then
      resMInt(
          mi(N, iMInt(sMInt(mi(N, I1))) %Int iMInt(sMInt(mi(N, I2)))),
          false,
          false)
    #else
      errMInt
    #fi
  rule
    uremMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    #if iMInt(uMInt(mi(N, I2))) =/=Int 0 #then 
      resMInt(
          mi(N, iMInt(uMInt(mi(N, I1))) %Int iMInt(uMInt(mi(N, I2)))),
          false,
          false)
    #else
      errMInt
    #fi

  /*
   * Bitwise operations
   */
  rule
    shlMInt(mi(N:Nat, I:Int), M:Nat)
  =>
    resMInt(
        sMInt(mi(N, iMInt(sMInt(mi(N, I))) <<Int M)),
        iMInt(sMInt(mi(N, I))) <<Int M <Int infMInt(N),
        iMInt(sMInt(mi(N, I))) <<Int M >Int supMInt(N))
  rule
    ushlMInt(mi(N:Nat, I:Int), M:Nat)
  =>
    resMInt(
        uMInt(mi(N, iMInt(uMInt(mi(N, I))) <<Int M)),
        false,
        iMInt(uMInt(mi(N, I))) <<Int M >Int usupMInt(N))

  rule
    shrMInt(mi(N:Nat, I:Int), M:Nat)
  =>
    resMInt(
        mi(N, iMInt(sMInt(mi(N, I))) >>Int M),
        false,
        false)
  rule
    ushrMInt(mi(N:Nat, I:Int), M:Nat)
  =>
    resMInt(
        mi(N, iMInt(uMInt(mi(N, I))) >>Int M),
        false,
        false)

  rule
    andMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(mi(N, I1 &Int I2), false, false)

  rule
    xorMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(mi(N, I1 xorInt I2), false, false)

  rule
    orMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    resMInt(mi(N, I1 |Int I2), false, false)

  rule
    ltMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(sMInt(mi(N, I1))) <Int iMInt(sMInt(mi(N, I2)))
  rule
    ultMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(uMInt(mi(N, I1))) <Int iMInt(uMInt(mi(N, I2)))

  rule
    leqMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(sMInt(mi(N, I1))) <=Int iMInt(sMInt(mi(N, I2)))
  rule
    uleqMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(uMInt(mi(N, I1))) <=Int iMInt(uMInt(mi(N, I2)))

  rule
    gtMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(sMInt(mi(N, I1))) >Int iMInt(sMInt(mi(N, I2)))
  rule
    ugtMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(uMInt(mi(N, I1))) >Int iMInt(uMInt(mi(N, I2)))

  rule
    geqMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(sMInt(mi(N, I1))) >=Int iMInt(sMInt(mi(N, I2)))
  rule
    geqMInt(mi(N:Nat, I1:Int), mi(N:Nat, I2:Int))
  =>
    iMInt(uMInt(mi(N, I1))) >=Int iMInt(uMInt(mi(N, I2)))

  rule
    mi(N:Nat, I1:Int) ==MInt mi(N:Nat, I2:Int)
  =>
    I1 modInt (1 <<Int N) ==Int I2 modInt (1 <<Int N)
  rule
    mi(N:Nat, I1:Int) =/=MInt mi(N:Nat, I2:Int)
  =>
    I1 modInt (1 <<Int N) =/=Int I2 modInt (1 <<Int N)
endmodule

