// Copyright (c) 2014 K Team. All Rights Reserved.
module INTEGER_LEMMAS
  imports INT-HOOKS

  rule 0 +Int I:Int => I
  rule I:Int +Int 0 => I

  rule 0 *Int _:Int => 0
  rule _:Int *Int 0 => 0
  rule 1 *Int I:Int => I
  rule I:Int *Int 1 => I
endmodule

module BOOLEAN_LEMMAS
  imports BOOL-HOOKS

  /* YilongL: already in bool.k but excluded by Java backend */
  rule true orBool _ => true
  rule _ orBool true => true
  rule false andBool _ => false
  rule _ andBool false => false
endmodule

module VERIFICATION_LEMMAS
  imports INTEGER_LEMMAS
  imports BOOLEAN_LEMMAS
endmodule
