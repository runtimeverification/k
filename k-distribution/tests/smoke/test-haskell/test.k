module TEST

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= "a" | "b" | "c" | "d" | "e"

    rule <k> a => b </k>
    rule <k> a => c </k>
    rule <k> c => d </k>
    rule <k> b => d </k>
endmodule
