// Copyright (c) 2020 K Team. All Rights Reserved.

module VERIFICATION-SYNTAX
  imports PROOFSYNTAX-SYNTAX
  syntax S ::= "e"
endmodule

module VERIFICATION
  imports VERIFICATION-SYNTAX
  imports PROOFSYNTAX
  syntax S ::= "f"
endmodule

module PROOFSYNTAX-SPEC-SYNTAX
  imports PROOFSYNTAX-SYNTAX
  syntax S ::= "g" // warning
endmodule

module PROOFSYNTAX-SPEC
  imports PROOFSYNTAX-SPEC-SYNTAX
  imports VERIFICATION
  syntax S ::= "h" // warning

  claim a => c requires false
endmodule
