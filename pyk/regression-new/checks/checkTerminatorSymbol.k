module CHECKTERMINATORSYMBOL
  imports INT
  syntax KItem ::= foo()
                 | bar() [terminator-symbol(bar)]

  syntax Ints ::= List{Int, ","} [symbol(ints), terminator-symbol(.ints)]

  syntax PipeInts ::= List{Int, "|"} [symbol(pipe-ints), terminator-symbol(.pipe-ints)]
  syntax Oops ::= oops() [symbol(.pipe-ints)]
endmodule
