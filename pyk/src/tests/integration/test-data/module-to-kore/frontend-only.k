module FRONTEND-ONLY-SYNTAX
    imports LIST

    syntax Foo ::= "foo"
                 | bar() [function, unused]
                 | baz() [function, public]
    syntax KResult ::= Foo
    syntax KItem ::= do(KItem) [hybrid, strict(1)]
endmodule

module FRONTEND-ONLY
    imports FRONTEND-ONLY-SYNTAX

    configuration <T>
        <k> $PGM:K </k>
        <out stream="stdout"> .List </out>
    </T>
endmodule
