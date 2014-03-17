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
  syntax Int ::= sinfMInt(Int)    [function]
               | ssupMInt(Int)    [function]
               | uinfMInt(Int)    [function]
               | usupMInt(Int)    [function]
  rule sinfMInt(N:Int) => 0 -Int (1 <<Int (N -Int 1))
  rule ssupMInt(N:Int) => (1 <<Int (N -Int 1)) -Int 1
  rule uinfMInt(_:Int) => 0 
  rule usupMInt(N:Int) => (1 <<Int N) -Int 1

  /*
   * Functions checking whether a given integer can be represented on as signed
   * or unsigned on a given bit width without overflow.
   */
  syntax Bool ::= soverflowMInt(Int, Int)   [function]
                | uoverflowMInt(Int, Int)   [function]
  rule
    soverflowMInt(N:Int, I:Int)
  =>
    I <Int sinfMInt(N) orBool I >Int ssupMInt(N)
  rule
    uoverflowMInt(N:Int, I:Int)
  =>
    I <Int uinfMInt(N) orBool I >Int usupMInt(N)

  /* Result of machine integer operations without overflow. */
  syntax MIntResult ::= MInt
                      | "errorMInt"   [function, hook(#MINT:error)]

  /* Projection functions for results of operations with overflow. */
  syntax MInt ::= miMInt(MyList)          [function]
  rule miMInt(MyListItem(MI:MInt), MyListItem(_:Bool)) => MI
  syntax Bool ::= overflowMInt(MyList)    [function]
  rule overflowMInt(MyListItem(_:MInt), MyListItem(B:Bool)) => B


  /* 
   * Arithmetic and comparison operations
   *   op   does not interprets th operands as either signed or unsigned 
   *   sop  interprets the operands as signed
   *   uop  interprets the operands as unsigned
   */
  syntax MInt ::= addMInt(MInt, MInt)   [function, hook(#MINT:add)]
                | subMInt(MInt, MInt)   [function, hook(#MINT:sub)]
                | mulMInt(MInt, MInt)   [function, hook(#MINT:mul)]

  /* Division and reminder. */
  syntax MIntResult ::= sdivMInt(MInt, MInt)    [function, hook(#MINT:sdiv)]
                      | udivMInt(MInt, MInt)    [function, hook(#MINT:udiv)]
                      | sremMInt(MInt, MInt)    [function, hook(#MINT:srem)]
                      | uremMInt(MInt, MInt)    [function, hook(#MINT:urem)]

  /* List of 2 elements representing a pair of result and overflow flag */
  syntax MyList ::= saddMInt(MInt, MInt)    [function, hook(#MINT:sadd)]
                  | uaddMInt(MInt, MInt)    [function, hook(#MINT:uadd)]
                  | ssubMInt(MInt, MInt)    [function, hook(#MINT:ssub)]
                  | usubMInt(MInt, MInt)    [function, hook(#MINT:usub)]
                  | smulMInt(MInt, MInt)    [function, hook(#MINT:smul)]
                  | umulMInt(MInt, MInt)    [function, hook(#MINT:umul)]

  /* Shift operations */
  syntax MIntResult ::= "shlMInt" "(" MInt "," Int ")"    [function]
                      | "ushlMInt" "(" MInt "," Int ")"   [function]
                      | "shrMInt" "(" MInt "," Int ")"    [function]
                      | "ushrMInt" "(" MInt "," Int ")"   [function]

  /* Bitwise operations */
  syntax MInt ::= andMInt(MInt, MInt)   [function, hook(#MINT:and)]
                | orMInt(MInt, MInt)    [function, hook(#MINT:or)]
                | xorMInt(MInt, MInt)   [function, hook(#MINT:xor)]

  /* Comparison operations */
  syntax Bool ::= sltMInt(MInt, MInt)   [function, hook(#MINT:slt)]
                | ultMInt(MInt, MInt)   [function, hook(#MINT:ult)]
                | sleMInt(MInt, MInt)   [function, hook(#MINT:sle)]
                | uleMInt(MInt, MInt)   [function, hook(#MINT:ule)]
                | sgtMInt(MInt, MInt)   [function, hook(#MINT:sgt)]
                | ugtMInt(MInt, MInt)   [function, hook(#MINT:ugt)]
                | sgeMInt(MInt, MInt)   [function, hook(#MINT:sge)]
                | ugeMInt(MInt, MInt)   [function, hook(#MINT:uge)]
                | MInt "==MInt" MInt    [function, hook(#MINT:eq)]
                | MInt "=/=MInt" MInt   [function, hook(#MINT:ne)]

  /* */
  //syntax MIntRes ::= "minMInt" "(" MInt "," MInt ")"    [function]
  //                 | "maxMInt" "(" MInt "," MInt ")"    [function]
  //                 | "absMInt" "(" MInt ")"             [function]

  syntax MyList ::= digitsOfMInt(MInt, Int)   [function, hook(#MINT:toDigits)]

  syntax MInt ::= mIntOfDigits(MyList, Int)   [function, hook(#MINT:fromDigits)]


//  rule bitwidthMInt(mi(N:Int, _)) => N 
//
//  rule
//    svalueMInt(mi(N:Int, I:Int))
//  =>
//    ((I +Int (1 <<Int (N -Int 1))) modInt (1 <<Int N)) -Int (1 <<Int (N -Int 1))
//  rule uvalueMInt(mi(N:Int, I:Int)) => I modInt (1 <<Int N)
//
//  rule zeroMInt(MI:MInt) => uvalueMInt(MI) ==Int 0
//
//  /*
//   * Arithmetic operations without overflow
//   */
//  rule addMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int)) => mi(N, I1 +Int I2)
//  rule subMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int)) => mi(N, I1 -Int I2)
//  rule mulMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int)) => mi(N, I1 *Int I2)
//
//  rule
//    sdivMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    #if notBool (svalueMInt(mi(N, I2)) ==Int 0
//            orBool (svalueMInt(mi(N, I1)) ==Int sinfMInt(N)
//                andBool svalueMInt(mi(N, I2)) ==Int -1))
//    #then
//      mi(N, svalueMInt(mi(N, I1)) /Int svalueMInt(mi(N, I2)))
//    #else
//      errorMInt
//    #fi
//  rule
//    udivMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    #if uvalueMInt(mi(N, I2)) =/=Int 0 #then
//      mi(N, uvalueMInt(mi(N, I1)) /Int uvalueMInt(mi(N, I2)))
//    #else
//      errorMInt
//    #fi
//
//  rule
//    sremMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    #if notBool (svalueMInt(mi(N, I2)) ==Int 0
//            orBool (svalueMInt(mi(N, I1)) ==Int sinfMInt(N)
//                andBool svalueMInt(mi(N, I2)) ==Int -1))
//    #then
//      mi(N, svalueMInt(mi(N, I1)) %Int svalueMInt(mi(N, I2)))
//    #else
//      errorMInt
//    #fi
//  rule
//    uremMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    #if uvalueMInt(mi(N, I2)) =/=Int 0 #then
//      mi(N, uvalueMInt(mi(N, I1)) %Int uvalueMInt(mi(N, I2)))
//    #else
//      errorMInt
//    #fi
//
//
//  /*
//   * Arithmetic operations with overflow
//   */
//  rule
//    saddMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    MyListItem(mi(N, I1 +Int I2)),
//    MyListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) +Int svalueMInt(mi(N, I2))))
//  rule
//    uaddMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    MyListItem(mi(N, I1 +Int I2)),
//    MyListItem(uoverflowMInt(N, uvalueMInt(mi(N, I1)) +Int uvalueMInt(mi(N, I2))))
//
//  rule
//    ssubMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    MyListItem(mi(N, I1 -Int I2)),
//    MyListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) -Int svalueMInt(mi(N, I2))))
//  rule
//    usubMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    MyListItem(mi(N, I1 -Int I2)),
//    MyListItem(uoverflowMInt(N, uvalueMInt(mi(N, I1)) -Int uvalueMInt(mi(N, I2))))
//
//  rule
//    smulMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    MyListItem(mi(N, I1 *Int I2)),
//    MyListItem(soverflowMInt(N, svalueMInt(mi(N, I1)) *Int svalueMInt(mi(N, I2))))
//  rule
//    umulMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    MyListItem(mi(N, I1 *Int I2)),
//    MyListItem(uoverflowMInt(N, uvalueMInt(mi(N, I1)) *Int uvalueMInt(mi(N, I2))))
//
//
//  /*
//   * Bitwise operations
//   */
//  rule andMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int)) => mi(N, I1 &Int I2)
//  rule orMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int)) => mi(N, I1 |Int I2)
//  rule xorMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int)) => mi(N, I1 xorInt I2)
//
//
//  /*
//   * Shift operations
//   */
////  rule
////    shlMInt(mi(N:Int, I:Int), M:Int)
////  =>
////    resMInt(
////        sMInt(mi(N, iMInt(sMInt(mi(N, I))) <<Int M)),
////        iMInt(sMInt(mi(N, I))) <<Int M <Int infMInt(N),
////        iMInt(sMInt(mi(N, I))) <<Int M >Int supMInt(N))
////  rule
////    ushlMInt(mi(N:Int, I:Int), M:Int)
////  =>
////    resMInt(
////        uMInt(mi(N, iMInt(uMInt(mi(N, I))) <<Int M)),
////        false,
////        iMInt(uMInt(mi(N, I))) <<Int M >Int usupMInt(N))
////
////  rule
////    shrMInt(mi(N:Int, I:Int), M:Int)
////  =>
////    resMInt(
////        mi(N, iMInt(sMInt(mi(N, I))) >>Int M),
////        false,
////        false)
////  rule
////    ushrMInt(mi(N:Int, I:Int), M:Int)
////  =>
////    resMInt(
////        mi(N, iMInt(uMInt(mi(N, I))) >>Int M),
////        false,
////        false)
//
//
//  /*
//   * Comparison operations
//   */
//  rule
//    sltMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    svalueMInt(mi(N, I1)) <Int svalueMInt(mi(N, I2))
//  rule
//    ultMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    uvalueMInt(mi(N, I1)) <Int uvalueMInt(mi(N, I2))
//
//  rule
//    sleMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    svalueMInt(mi(N, I1)) <=Int svalueMInt(mi(N, I2))
//  rule
//    uleMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    uvalueMInt(mi(N, I1)) <=Int uvalueMInt(mi(N, I2))
//
//  rule
//    sgtMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    svalueMInt(mi(N, I1)) >Int svalueMInt(mi(N, I2))
//  rule
//    ugtMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    uvalueMInt(mi(N, I1)) >Int uvalueMInt(mi(N, I2))
//
//  rule
//    sgeMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    svalueMInt(mi(N, I1)) >=Int svalueMInt(mi(N, I2))
//  rule
//    ugeMInt(mi(N:Int, I1:Int), mi(N:Int, I2:Int))
//  =>
//    uvalueMInt(mi(N, I1)) >=Int uvalueMInt(mi(N, I2))
//
//  rule
//    mi(N:Int, I1:Int) ==MInt mi(N:Int, I2:Int)
//  =>
//    (I1 modInt (1 <<Int N)) ==Int (I2 modInt (1 <<Int N))
//  rule
//    mi(N:Int, I1:Int) =/=MInt mi(N:Int, I2:Int)
//  =>
//    (I1 modInt (1 <<Int N)) =/=Int (I2 modInt (1 <<Int N))
//
//  rule digitsOfMInt(MI:MInt, N:Int) => digitsOfMIntHelper(uvalueMInt(Int), N)
//  syntax MyList ::= digitsOfMIntHelper(Int, Int)    [function]
//  rule
//    digitsOfMIntHelper(I:Int, N:Int)
//  =>
//    #if (I =/=Int 0) #then
//      digitsOfMIntHelper(I >>Int N, N), MyListItem(mi(N, I %Int (1 <<Int N)))
//    #else
//      .MyList
//    #fi
//
//  rule
//    mIntOfDigits((MyListItem(MI:MInt), L:MyList), N:Int)
//  =>
//    (mIntOfDigits(L, N) <<Int N) +Int uvalueMInt(MI)
//  when bitwidthMInt(MI) ==Int N
endmodule

