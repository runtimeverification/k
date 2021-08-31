module LAMBDA-SYNTAX
  imports ID-SYNTAX

  syntax Exp  ::= Id
                | "lambda" Id "." Exp
                | Exp Exp [left]
                | "(" Exp ")" [bracket]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
endmodule
