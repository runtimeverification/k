module REGEX-TERMINAL-SYNTAX
    syntax T0 ::= r"b"            [token]
    syntax T1 ::= r"(?<!a)b"      [token]
    syntax T2 ::= r"b(?!c)"       [token]
    syntax T3 ::= r"(?<!a)b(?!c)" [token]
endmodule


module REGEX-TERMINAL
    imports REGEX-TERMINAL-SYNTAX
endmodule
