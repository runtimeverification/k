module INVALIDSYMBOL

syntax Foo ::= foo() [klabel(#KToken), symbol]

syntax Bar ::= bar() [klabel(foo), symbol]
syntax Baz ::= baz() [klabel(foo), symbol]

endmodule
