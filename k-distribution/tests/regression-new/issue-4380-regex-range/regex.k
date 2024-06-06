
module REGEX-SYNTAX

    syntax Foo ::= r"[a]{1,6}" [token]

endmodule


module REGEX
    imports REGEX-SYNTAX
    imports INT

    configuration <k> $PGM:Foo </k>

endmodule
