// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "int.k"

module ARRAY-SYNTAX
  imports K-TECHNIQUE
  syntax Array ::= "store"       "(" Array "," Int "," K ")"  [smtlib(store)]
                  | "const-array" "(" Int "," K ")"

  syntax KItem ::= "select" "(" Array "," Int ")"  [smtlib(select)]

  syntax Int ::= "size-of-array" "(" Array ")" [function, symbolic-function]
endmodule


module ARRAY
  imports ARRAY-SYNTAX
  imports K-EQUAL-HOOKS
  imports INT-HOOKS
  imports BOOL-HOOKS
  imports STRING-HOOKS

  // main array axioms
  rule select(store(_:Array, I:Int, V:K), J:Int) => V
       when I ==Int J [symbolic-kompile]
  rule select(store(A:Array, I:Int, _:K), J:Int) => select(A, J)
       when I =/=Int J [symbolic-kompile]

  // select from constant array
  rule select(const-array(Size:Int, V:K), I:Int) => V
       when (0 <=Int I) andBool (I <Int Size) [symbolic-kompile]

  // simplification of multiple store
  rule store(store(A:Array, I:Int, V:K), J:Int, V':K)
       =>
       store(store(A, J, V':K), I, V)
       when J <Int I
       [anywhere]

  rule store(store(A:Array, I:Int, _:K), I, V:K)
       =>
       store(A, I, V)
       [anywhere]

  // array size
  rule size-of-array(store(A:Array, _:K, _:K)) => size-of-array(A)
  rule size-of-array(const-array(Size:Int, _:K)) => Size

endmodule
