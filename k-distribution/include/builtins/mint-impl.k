// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "mint.k"

module MINT-IMPL
  imports MINT

  syntax MInt ::= "$mi" "(" Int "," Int ")"
  rule mi(I1, I2) => $mi(I1, I2)

  /* Implementation with K rules */
  rule bitwidthMInt($mi(N:Int, _)) => N

  rule
    svalueMInt($mi(N:Int, I:Int))
  =>
    ((I +Int (1 <<Int (N -Int 1))) modInt (1 <<Int N)) -Int (1 <<Int (N -Int 1))
  rule uvalueMInt($mi(N:Int, I:Int)) => I modInt (1 <<Int N)

  /*
   * Arithmetic operations without overflow
   */
  rule addMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int)) => mi(N, I1 +Int I2)
  rule subMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int)) => mi(N, I1 -Int I2)
  rule mulMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int)) => mi(N, I1 *Int I2)

  rule
    sdivMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, svalueMInt(mi(N, I1)) /Int svalueMInt(mi(N, I2))))
    ListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) /Int svalueMInt(mi(N, I2))))
  when notBool zeroMInt(mi(N, I2))
  rule
    sremMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, svalueMInt(mi(N, I1)) %Int svalueMInt(mi(N, I2))))
    ListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) /Int svalueMInt(mi(N, I2))))
  when notBool zeroMInt(mi(N, I2))


  rule
    udivMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    mi(N, uvalueMInt(mi(N, I1)) /Int uvalueMInt(mi(N, I2)))
  when notBool zeroMInt(mi(N, I2))
  rule
    uremMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    mi(N, uvalueMInt(mi(N, I1)) %Int uvalueMInt(mi(N, I2)))
  when notBool zeroMInt(mi(N, I2))

  /*
   * Arithmetic operations with overflow
   */
  rule
    saddMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, I1 +Int I2))
    ListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) +Int svalueMInt(mi(N, I2))))
  rule
    uaddMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, I1 +Int I2))
    ListItem(uoverflowMInt(N, uvalueMInt(mi(N, I1)) +Int uvalueMInt(mi(N, I2))))

  rule
    ssubMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, I1 -Int I2))
    ListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) -Int svalueMInt(mi(N, I2))))
  rule
    usubMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, I1 -Int I2))
    ListItem(uoverflowMInt(N, uvalueMInt(mi(N, I1)) -Int uvalueMInt(mi(N, I2))))

  rule
    smulMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, I1 *Int I2))
    ListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) *Int svalueMInt(mi(N, I2))))
  rule
    umulMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    ListItem(mi(N, I1 *Int I2))
    ListItem(uoverflowMInt(N, uvalueMInt(mi(N, I1)) *Int uvalueMInt(mi(N, I2))))

  /*
   * Bitwise operations
   */
  rule andMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int)) => mi(N, I1 &Int I2)
  rule orMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int)) => mi(N, I1 |Int I2)
  rule xorMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int)) => mi(N, I1 xorInt I2)

  /*
   * Shift operations
   */
  rule shlMInt($mi(N:Int, I:Int), M:Int) => mi(N, I <<Int M)
  rule ashrMInt($mi(N:Int, I:Int), M:Int) => mi(N, I >>Int M)
  rule lshrMInt($mi(N:Int, I:Int), M:Int) => mi(N, (I &Int umaxMInt(N)) >>Int M)

  /*
   * Comparison operations
   */
  rule
    sltMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    svalueMInt(mi(N, I1)) <Int svalueMInt(mi(N, I2))
  rule
    ultMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    uvalueMInt(mi(N, I1)) <Int uvalueMInt(mi(N, I2))

  rule
    sleMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    svalueMInt(mi(N, I1)) <=Int svalueMInt(mi(N, I2))
  rule
    uleMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    uvalueMInt(mi(N, I1)) <=Int uvalueMInt(mi(N, I2))

  rule
    sgtMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    svalueMInt(mi(N, I1)) >Int svalueMInt(mi(N, I2))
  rule
    ugtMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    uvalueMInt(mi(N, I1)) >Int uvalueMInt(mi(N, I2))

  rule
    sgeMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    svalueMInt(mi(N, I1)) >=Int svalueMInt(mi(N, I2))
  rule
    ugeMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    uvalueMInt(mi(N, I1)) >=Int uvalueMInt(mi(N, I2))

  rule
    eqMInt($mi(N:Int, I1:Int),  $mi(N:Int, I2:Int))
  =>
    (I1 modInt (1 <<Int N)) ==Int (I2 modInt (1 <<Int N))
  rule
    neMInt($mi(N:Int, I1:Int), $mi(N:Int, I2:Int))
  =>
    (I1 modInt (1 <<Int N)) =/=Int (I2 modInt (1 <<Int N))

  /*
   * Composition and decomposition
   */
  rule
    concatenateMInt($mi(N1:Int, I1:Int), $mi(N2:Int, I2:Int))
  =>
    mi(N1 +Int N2, (I1 <<Int N2) |Int (I2 &Int umaxMInt(N2)))
  rule
    extractMInt($mi(N:Int, I:Int), M1:Int, M2:Int)
  =>
    mi(M2 -Int M1, (I >>Int (N -Int M2)) &Int umaxMInt(M2 -Int M1))
  when (M1 <Int M2) andBool (M1 <=Int N) andBool (M2 <=Int N)
endmodule

