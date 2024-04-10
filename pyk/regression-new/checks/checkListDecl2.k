// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module CHECKLISTDECL2-SYNTAX
    syntax Pgm
endmodule

module CHECKLISTDECL2
    imports CHECKLISTDECL2-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax Int ::= List{Int,""}

endmodule
