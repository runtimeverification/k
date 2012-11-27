// header
module IMP-SYNTAX
  syntax AExp ::= Int | Id
                | AExp "/" AExp    [left, strict]
                > AExp "+" AExp    [left, strict]

  syntax priorities
          a 'a >
          b c d >
          z
  syntax left a
  syntax right b
  syntax non-assoc c

endmodule
