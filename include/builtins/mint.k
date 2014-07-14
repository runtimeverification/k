// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "int.k"
require "k-equal.k"
require "list.k"


/*
 * Module implementing machine integers of arbitrary bit width represented in
 * 2's complement.
 */
module MINT
  imports INT-HOOKS
  imports K-EQUAL-HOOKS
  imports LIST

  /* Machine integer of bit width and value. */
  syntax MInt ::= mi(Int, Int)    [function, hook(#MINT:constructor)]

  syntax MInt ::= "$mi" "(" Int "," Int ")"
  rule mi(I1, I2) => $mi(I1, I2)

  /* Function returning the bit width of this machine integer. */
  syntax Int ::= bitwidthMInt(MInt)   [function, hook(#MINT:bitwidth)]

  /*
   * Functions returning the signed and unsigned interpretations of this
   * machine integers.
   *   svalue  returns an integer between -2^(bitwidth - 1) and
   *           2^(bitwidth - 1) - 1
   *   uvalue  returns an integer between 0 and 2^bitwidth - 1
   */
  syntax Int ::= svalueMInt(MInt)     [function, hook(#MINT:svalue)]
               | uvalueMInt(MInt)     [function, hook(#MINT:uvalue)]

  /* Checks whether a machine integer is zero */
  syntax Bool ::= zeroMInt(MInt)    [function, hook(#MINT:zero)]

  /*
   * Functions for signed and unsigned minimum and maximum values of a machine
   * integer on a given bit width.
   */
  syntax Int ::= sminMInt(Int)    [function]
               | smaxMInt(Int)    [function]
               | uminMInt(Int)    [function]
               | umaxMInt(Int)    [function]
  rule sminMInt(N:Int) => 0 -Int (1 <<Int (N -Int 1))
  rule smaxMInt(N:Int) => (1 <<Int (N -Int 1)) -Int 1
  rule uminMInt(_:Int) => 0 
  rule umaxMInt(N:Int) => (1 <<Int N) -Int 1

  /*
   * Functions checking whether a given integer can be represented on as signed
   * or unsigned on a given bit width without overflow.
   */
  syntax Bool ::= soverflowMInt(Int, Int)   [function]
                | uoverflowMInt(Int, Int)   [function]
  rule
    soverflowMInt(N:Int, I:Int)
  =>
    I <Int sminMInt(N) orBool I >Int smaxMInt(N)
  rule
    uoverflowMInt(N:Int, I:Int)
  =>
    I <Int uminMInt(N) orBool I >Int umaxMInt(N)

  /*
   * Projection functions for results of operations with overflow.
   * miInt(saddMInt(...))         returns the result of the operation (ignoring
   *                              overflow)
   * overflowMInt(saddMInt(...))  returns true if overflow is detected during
   *                              the execution of the operation
   */
  syntax MInt ::= miMInt(List)          [function]
  rule miMInt(ListItem(MI:MInt) ListItem(_:Bool)) => MI
  syntax Bool ::= overflowMInt(List)    [function]
  rule overflowMInt(ListItem(_:MInt) ListItem(B:Bool)) => B

  /* 
   * Arithmetic and comparison operations
   *   op   does not interprets th operands as either signed or unsigned 
   *   sop  interprets the operands as signed
   *   uop  interprets the operands as unsigned
   */
  /*
   * Addition, subtraction, and multiplication are the same for signed and
   * unsigned integers represented in 2's complement
   */
  syntax MInt ::= addMInt(MInt, MInt)   [function, hook(#MINT:add)]
                | subMInt(MInt, MInt)   [function, hook(#MINT:sub)]
                | mulMInt(MInt, MInt)   [function, hook(#MINT:mul)]

  /*
   * Division and reminder
   * sdiv/srem  operation interprets operands as signed; undefined if the second
   *            argument is 0; returns a pair of result and overflow flag
   *            represented as a list of 2 elements (overflow happens when the
   *            first operand is the minimum value and the second operand is -1)
   * udiv/urem  operation interprets operands as unsigned; undefined if the
   *            second argument is 0 
   */
  syntax List ::= sdivMInt(MInt, MInt)    [function, hook(#MINT:sdiv)]
                | sremMInt(MInt, MInt)    [function, hook(#MINT:srem)]
  syntax MInt ::= udivMInt(MInt, MInt)    [function, hook(#MINT:udiv)]
                | uremMInt(MInt, MInt)    [function, hook(#MINT:urem)]

  /*
   * Addition, subtraction and multiplication with overflow detection; each
   * operation returns a pair of result and overflow flag represented as a list
   * of 2 elements
   */
  syntax List ::= saddMInt(MInt, MInt)    [function, hook(#MINT:sadd)]
                | uaddMInt(MInt, MInt)    [function, hook(#MINT:uadd)]
                | ssubMInt(MInt, MInt)    [function, hook(#MINT:ssub)]
                | usubMInt(MInt, MInt)    [function, hook(#MINT:usub)]
                | smulMInt(MInt, MInt)    [function, hook(#MINT:smul)]
                | umulMInt(MInt, MInt)    [function, hook(#MINT:umul)]

  /* Shift operations; the second operand must be non-negative */
  syntax MInt ::= shlMInt(MInt, Int)    [function, hook(#MINT:shl)]
                | ashrMInt(MInt, Int)   [function, hook(#MINT:ashr)]
                | lshrMInt(MInt, Int)   [function, hook(#MINT:lshr)]

  /* Bitwise operations */
  syntax MInt ::= andMInt(MInt, MInt)   [function, hook(#MINT:and)]
                | orMInt(MInt, MInt)    [function, hook(#MINT:or)]
                | xorMInt(MInt, MInt)   [function, hook(#MINT:xor)]

  syntax MInt ::= negMInt(MInt)   [function]
  rule negMInt(MI:MInt) => xorMInt(MI, mi(bitwidthMInt(MI), 0))

  /* Comparison operations */
  syntax Bool ::= sltMInt(MInt, MInt)   [function, hook(#MINT:slt)]
                | ultMInt(MInt, MInt)   [function, hook(#MINT:ult)]
                | sleMInt(MInt, MInt)   [function, hook(#MINT:sle)]
                | uleMInt(MInt, MInt)   [function, hook(#MINT:ule)]
                | sgtMInt(MInt, MInt)   [function, hook(#MINT:sgt)]
                | ugtMInt(MInt, MInt)   [function, hook(#MINT:ugt)]
                | sgeMInt(MInt, MInt)   [function, hook(#MINT:sge)]
                | ugeMInt(MInt, MInt)   [function, hook(#MINT:uge)]
                | eqMInt(MInt, MInt)    [function, hook(#MINT:eq)]
                | neMInt(MInt, MInt)    [function, hook(#MINT:ne)]

  /*
   * Returns a machine integer with the underlying bits the bits of the first
   * machine integer concatenated with the bits of the second machine integer.
   * The bits of the first machine integer are on the more significant
   * positions.
   */
  syntax MInt ::= concatenateMInt(MInt, MInt)   [function, hook(#MINT:concatenate)]

  /*
   * Returns a machine integer with the underlying bits the bits of the given
   * machine integer in the given range. The bit on position 0 is the most
   * significant bit.
   */
  syntax MInt ::= extractMInt(MInt, Int, Int)   [function, hook(#MINT:extract)]

  /*
   * Returns a list of the first digits representing the given machine integer,
   * each digit a machine integer on the given bitwidth. Useful for serializing
   * a integer to a sequence of bytes.
   */
  syntax List ::= digitsOfMInt(MInt, Int, Int)   [function, hook(#MINT:toDigits)]

  /*
   * Returns a machine integer representing the given list of digits. Each digit
   * is represented as a machine integers. The list must be non-empty. Useful
   * for deserializing an integer from a sequence of bytes.
   */
  syntax MInt ::= mIntOfDigits(List)   [function, hook(#MINT:fromDigits)]


  /* Implementation with K rules */
  rule bitwidthMInt($mi(N:Int, _)) => N 

  rule
    svalueMInt($mi(N:Int, I:Int))
  =>
    ((I +Int (1 <<Int (N -Int 1))) modInt (1 <<Int N)) -Int (1 <<Int (N -Int 1))
  rule uvalueMInt($mi(N:Int, I:Int)) => I modInt (1 <<Int N)

  // TODO(AndreiS): change
  rule zeroMInt(MI:MInt) => eqMInt(MI, xorMInt(MI, MI))

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

  /*
   * Conversion to and from a list of digits
   */
  rule
    digitsOfMInt(MI:MInt, N:Int, M:Int)
  =>
    digitsOfMInt(MI, N, M -Int 1)
    ListItem(extractMInt(MI, (N *Int (M -Int 1)), (N *Int M)))
  when M >Int 0
  rule digitsOfMInt(_:MInt, _:Int, 0) => .List

  rule
    mIntOfDigits(ListItem(MI1:MInt) ListItem(MI2:MInt) L:List)
  =>
    concatenateMInt(MI1, mIntOfDigits(ListItem(MI2) L))
  rule mIntOfDigits(ListItem(MI:MInt)) => MI
endmodule

