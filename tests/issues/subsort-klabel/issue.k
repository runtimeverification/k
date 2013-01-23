module ISSUE

syntax Foo ::= Bar [klabel('foo)]
syntax Bar ::= "bar"
syntax Baz ::= "baz" Foo

rule X:Baz => .

endmodule
