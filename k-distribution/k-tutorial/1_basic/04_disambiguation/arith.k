module ARITH

  syntax Integer  ::= r"[1-9][0-9]*" [token]
                    | "(" Integer ")" [bracket]
                    > "-" Integer [function]
                    > left: Integer "*" Integer [function]
                    | Integer "/" Integer [function]
                    > left: Integer "+" Integer [function]
                    | Integer "-" Integer [function]

endmodule
