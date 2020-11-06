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
  rule bar2(2) => 2 [simplification]

  syntax Int ::= baz(Int) [function]
  rule baz(0) => 0 [concrete]
  rule baz(1) => 1 [simplification]

  syntax Int ::= baz2(Int) [function]
  rule baz2(0) => 0 [concrete]
  rule baz2(1) => 1

  syntax Int ::= baz3(Int) [function]
  rule baz3(X) => 0 [concrete(X)]
endmodule
