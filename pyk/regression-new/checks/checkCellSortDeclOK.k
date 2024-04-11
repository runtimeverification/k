// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module CHECKCELLSORTDECLOK-SYNTAX
    syntax Pgm
endmodule

module CHECKCELLSORTDECLOK
    imports CHECKCELLSORTDECLOK-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax Pgm ::= KCell

endmodule
