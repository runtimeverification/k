requires "domains.md"
requires "json.md"

module TEST-SYNTAX
  imports COLLECTIONS
  imports RANGEMAP
  imports INT
  imports JSON

  syntax RangeMap ::= rangemap (Int) [function]
// ---------------------------------------
  rule rangemap(0) => .RangeMap
  rule rangemap(1) => range(0, 1) r|-> 40
  rule rangemap(2) => range(1, 2) r|-> 50
  rule rangemap(3) => range(0, 1) r|-> 45 range(3, 5) r|-> 53
  rule rangemap(4) => range(0, 1) r|-> 45 range(1, 5) r|-> 50
  rule rangemap(5) => range(0, 1) r|-> 0 range(1, 2) r|-> 1
endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:KItem </k>
endmodule
