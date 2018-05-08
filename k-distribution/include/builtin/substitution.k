// Copyright (c) 2015-2018 K Team. All Rights Reserved.

module SUBSTITUTION
  imports MAP

  // used for user-defined substitution only
  syntax KVariable

  syntax K ::= K "[" K "/" K "]"  [function, hook(SUBSTITUTION.substOne), impure, poly(0, 1)]
  syntax K ::= K "[" Map "]"      [function, hook(SUBSTITUTION.substMany), impure, poly(0, 1)]
endmodule
