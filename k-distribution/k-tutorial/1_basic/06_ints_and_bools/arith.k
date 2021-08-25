module ARITH-SYNTAX
  imports INT-SYNTAX
  syntax Integer  ::= Int
                    | "(" Integer ")" [bracket]
                    > "-" Integer [function]
                    > left: Integer "*" Integer [function]
                    | Integer "/" Integer [function]
                    > left: Integer "+" Integer [function]
                    | Integer "-" Integer [function]
endmodule

module ARITH
  imports INT
  imports ARITH-SYNTAX

  rule - N => 0 -Int N
  rule N * M => N *Int M
  rule N / M => N /Int M
  rule N + M => N +Int M
  rule N - M => N -Int M
endmodule
