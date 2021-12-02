module INVALIDFORMAT

  syntax Foo ::= "foo" [format(%)]

  syntax Bar ::= "bar" [format(%c), colors(black)]

  syntax Baz ::= "baz" [format(%%%%c), colors(white)]
endmodule
