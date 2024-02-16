module KLABEL
    syntax Foo ::= "foo" [symbol(foo)]
                 | "bar" [klabel(bar), symbol]
                 | "baz" [klabel(baz)]
                 | "qux"
endmodule
