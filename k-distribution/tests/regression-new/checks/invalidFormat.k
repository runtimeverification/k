module INVALIDFORMAT

  syntax Foo ::= "foo" [format(%)]

  syntax Bar ::= "bar" [format(%c), colors(black)]

  syntax Baz ::= "baz" [format(%%%%c), colors(white)]

  syntax A ::= "a" [format(%0)]

  syntax B ::= "b" [format(%2)]

  syntax C ::= r"c" [format(%1)]

  syntax D ::= r"d"

  syntax E ::= r"e" "f"
endmodule
