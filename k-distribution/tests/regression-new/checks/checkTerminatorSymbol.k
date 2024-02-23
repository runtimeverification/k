module CHECKTERMINATORSYMBOL
  imports INT
  syntax KItem ::= foo()
                 | bar() [terminator-symbol(bar)]

  syntax Ints ::= List{Int, ","} [symbol(ints), terminator-symbol(.ints)]
endmodule
