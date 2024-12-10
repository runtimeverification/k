module IMPURE-SYNTAX
    syntax Foo ::= "foo" [token]
                 | bar() [function, impure]
                 | baz() [function]
                 | qux() [function]
endmodule

module IMPURE
    imports IMPURE-SYNTAX

    rule bar() => foo
    rule baz() => bar()
    rule qux() => foo
endmodule
