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

  rule rangemap(1) => [0, 20) r|-> 40
  rule rangemap(2) => [2, 3) r|-> 40
  rule rangemap(3) => [17, 19) r|-> 40

  rule rangemap(4) => [1, 2) r|-> 40 [3, 5) r|-> 40
  rule rangemap(5) => [1, 2) r|-> 45 [3, 5) r|-> 40
  rule rangemap(6) => [0, 1) r|-> 40 [4, 5) r|-> 40

  rule rangemap(7) => [1, 2) r|-> 40 [5, 7) r|-> 40 [9, 12) r|-> 40
  rule rangemap(8) => [0, 2) r|-> 40 [3, 8) r|-> 40 [9, 12) r|-> 45

  rule rangemap(9) => [0, 1) r|-> 40 [2, 5) r|-> 40 [7, 9) r|-> 40 [12, 15) r|-> 40
  rule rangemap(10) => [1, 3) r|-> 45 [4, 6) r|-> 50 [8, 9) r|-> 40 [12, 15) r|-> 45
endmodule

module RANGEMAP-SIMPLE
  imports RANGEMAP-SIMPLE-SYNTAX

  configuration <k> $PGM:KItem </k>
endmodule
