requires "domains.md"
requires "json.md"

module RANGEMAP-SIMPLE-SYNTAX
  imports COLLECTIONS
  imports RANGEMAP
  imports INT
  imports JSON

  syntax RangeMap ::= rangemap (Int) [function]
// ---------------------------------------
  rule rangemap(0) => .RangeMap

  rule rangemap(1) => range(0, 20) r|-> 40
  rule rangemap(2) => range(2, 3) r|-> 40
  rule rangemap(3) => range(17, 19) r|-> 40

  rule rangemap(4) => range(1, 2) r|-> 40 range(3, 5) r|-> 40
  rule rangemap(5) => range(1, 2) r|-> 45 range(3, 5) r|-> 40
  rule rangemap(6) => range(0, 1) r|-> 40 range(4, 5) r|-> 40

  rule rangemap(7) => range(1, 2) r|-> 40 range(5, 7) r|-> 40 range(9, 12) r|-> 40
  rule rangemap(8) => range(0, 2) r|-> 40 range(3, 8) r|-> 40 range(9, 12) r|-> 45

  rule rangemap(9) => range(0, 1) r|-> 40 range(2, 5) r|-> 40 range(7, 9) r|-> 40 range(12, 15) r|-> 40
  rule rangemap(10) => range(1, 3) r|-> 45 range(4, 6) r|-> 50 range(8, 9) r|-> 40 range(12, 15) r|-> 45
endmodule

module RANGEMAP-SIMPLE
  imports RANGEMAP-SIMPLE-SYNTAX

  configuration <k> $PGM:KItem </k>
endmodule
