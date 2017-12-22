// Copyright (c) 2015-2016 K Team. All Rights Reserved.

module SUBSTITUTION
  imports MAP

  // used for user-defined substitution only
  syntax KVariable

  syntax K ::= K "[" K "/" K "]"  [function, hook(SUBSTITUTION.userSingletonSubstitutionKore), impure]
  syntax K ::= K "[" Map "]"      [function, hook(SUBSTITUTION.userSubstitutionKore), impure]
endmodule
