// header
module IMP-SYNTAX
  syntax AExp ::= Int | Id
                | AExp "/" AExp    [left, strict]
                > AExp "+" AExp    [left, strict]

  syntax priorities
         left:      a 'a >
         non-assoc: b c d >
                    z


endmodule
