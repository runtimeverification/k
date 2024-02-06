module CHECKTERMINATORKLABEL
  imports INT
  syntax KItem ::= foo()
                 | bar() [terminator-klabel(bar)]

  syntax Ints ::= List{Int, ","} [klabel(ints), terminator-klabel(.ints), symbol]
endmodule