// Copyright (c) 2019 K Team. All Rights Reserved.

module INT-PARSE-SYNTAX
    imports INT
    imports STRING
    syntax Pgm ::= intparse ( String )
endmodule

module INT-PARSE
    imports INT-PARSE-SYNTAX

    configuration <k> $PGM:Pgm </k>

    rule <k> intparse ( I ) => String2Base ( I , 10) ... </k>
endmodule
