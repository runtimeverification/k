module TEST
    imports INT
    syntax X ::= "a"
    configuration <k> $PGM:X </k>
    rule <k> a => ?_:Int </k>
    syntax Bool ::= pred1 ( Int ) [function, functional, klabel(pred1), symbol, no-evaluators]
endmodule
