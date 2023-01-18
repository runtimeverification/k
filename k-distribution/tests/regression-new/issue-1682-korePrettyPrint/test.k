// Copyright (c) K Team. All Rights Reserved.
module TEST
    imports INT
    syntax X ::= "a"
    configuration <k> $PGM:X </k>
    rule <k> a => ?_:Int </k>
    syntax Bool ::= pred1 ( Int ) [function, total, klabel(pred1), symbol, no-evaluators]
endmodule
