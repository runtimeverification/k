module LESSON-03-A

  syntax Boolean  ::= "true" | "false"
                    | "!" Boolean [function]
                    | Boolean "&&" Boolean [function]
                    | Boolean "^" Boolean [function]
                    | Boolean "||" Boolean [function]
                    | "(" Boolean ")" [bracket]

endmodule
