// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module CHECKLISTDECL3-SYNTAX
    syntax Pgm
endmodule

module CHECKLISTDECL3
    imports CHECKLISTDECL3-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax KItem ::= Int "+" List{Int,""}

endmodule
