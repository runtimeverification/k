// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module CHECKLISTDECL1-SYNTAX
    syntax Pgm
endmodule

module CHECKLISTDECL1
    imports CHECKLISTDECL1-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax KItem ::= List{Int,""}

endmodule
