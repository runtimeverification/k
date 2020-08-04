module CONCRETE
  imports INT

  rule 0 +Int X => X [symbolic, simplification]
  rule 1 +Int X => X +Int 1 [concrete, simplification]
  rule 0 *Int X => 0 [symbolic]
  rule 1 *Int X => X [concrete]

  syntax Int ::= foo(Int) [function]
  rule foo(0) => 0 [symbolic, concrete]

  syntax Int ::= bar(Int) [function]
  rule bar(0) => 0 [symbolic]

  syntax Int ::= bar2(Int) [function]
  rule bar2(0) => 0 [symbolic]
  rule bar2(1) => 1

  syntax Int ::= baz(Int) [function]
  rule baz(0) => 0 [concrete]

  syntax Int ::= baz2(Int) [function]
  rule baz2(0) => 0 [concrete]
  rule baz2(1) => 1

endmodule
