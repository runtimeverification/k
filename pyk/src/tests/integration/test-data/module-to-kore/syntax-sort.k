module FOO
    syntax Foo ::= "foo"
endmodule

module BAR
    syntax Foo
    syntax Foo
endmodule

module SYNTAX-SORT-SYNTAX
    syntax Foo
endmodule

module SYNTAX-SORT
    imports SYNTAX-SORT-SYNTAX
    imports FOO
    imports BAR
endmodule
