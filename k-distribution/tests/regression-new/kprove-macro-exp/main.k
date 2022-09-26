module DATA
    imports INT
    imports BOOL

    syntax Bool ::= #range ( Int, Int ) [macro]
    rule #range(5, I) => 0 <=Int I andBool I <Int 32
    rule #range(8, I) => 0 <=Int I andBool I <Int 256
endmodule

module MAIN
    imports DATA

    configuration <k> $PGM:Pgm </k>
                  <unused> .K </unused>

    syntax Pgm ::= "a" | "b"

    rule <k> a => b ... </k>

endmodule
