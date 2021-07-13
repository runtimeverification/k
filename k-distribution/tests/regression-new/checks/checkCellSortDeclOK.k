// Copyright (c) 2016-2021 K Team. All Rights Reserved.

module CHECKCELLSORTDECLOK-SYNTAX
    syntax Pgm
endmodule

module CHECKCELLSORTDECLOK
    imports CHECKCELLSORTDECLOK-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax Pgm ::= KCell

endmodule
