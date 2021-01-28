module TEST
    imports INT
    syntax X ::= "a"
    configuration <k> $PGM:X </k>
    rule <k> a => ?_:Int </k>
endmodule
