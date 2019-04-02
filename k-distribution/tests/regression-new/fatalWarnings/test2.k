module TEST2-SYNTAX

endmodule

module TEST2
  imports TEST2-SYNTAX

  syntax Foo ::= "foo" [klabel(foo), symbol]
  syntax Bar ::= "foo" [klabel(bar), symbol]

  rule foo => 0
endmodule
