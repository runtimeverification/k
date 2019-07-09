// Copyright (c) 2019 K Team. All Rights Reserved.

module FLOAT-MUL-SYNTAX
    imports FLOAT
    syntax Pgm ::= f32mul ( Float, Float )
                 | checkEqual ( Float )
                 | Pgm ";" Pgm
endmodule

module FLOAT-MUL
    imports FLOAT-MUL-SYNTAX

    configuration <k> $PGM:Pgm </k>

    rule <k> f32mul ( F1, F2 ) => roundFloat(F1, 24, 8) *Float roundFloat(F2, 24, 8) ... </k>
    rule <k> F1:Float ~> checkEqual ( F2 ) => . ... </k> requires F1 ==Float roundFloat(F2, 24, 8)
    rule <k> P1 ; P2 => P1 ~> P2 ... </k>
endmodule
