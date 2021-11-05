module UNEXPANDEDMACRO
  imports INT

  syntax Int ::= A ( Int ) [macro]
  rule A ( N ) +Int 4 => N
endmodule
