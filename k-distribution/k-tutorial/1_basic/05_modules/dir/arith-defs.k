module ATOM-SYNTAX
  syntax Integer  ::= r"[1-9][0-9]*" [literal, token]
                    | "(" Integer ")" [atom, bracket]
endmodule

module ADD-SYNTAX
  syntax Integer  ::= "-" Integer [unary, function]
                    | Integer "+" Integer [addop, function]
                    | Integer "-" Integer [addop, function]
endmodule

module MUL-SYNTAX
  syntax Integer  ::= Integer "*" Integer [mulop, function]
                    | Integer "/" Integer [mulop, function]
endmodule
