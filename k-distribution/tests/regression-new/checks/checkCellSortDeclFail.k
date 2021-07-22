// Copyright (c) 2016-2021 K Team. All Rights Reserved.

module CHECKCELLSORTDECLFAIL-SYNTAX
    syntax Pgm
endmodule

module CHECKCELLSORTDECLFAIL
    imports CHECKCELLSORTDECLFAIL-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax Pgm ::= MisTypedCell

endmodule
