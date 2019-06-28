// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module CHECKLISTDECL2-SYNTAX
    syntax Pgm
endmodule

module CHECKLISTDECL2
    imports CHECKLISTDECL2-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax Int ::= List{Int,""}

endmodule
