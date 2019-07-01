// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module CHECKLISTDECL1-SYNTAX
    syntax Pgm
endmodule

module CHECKLISTDECL1
    imports CHECKLISTDECL1-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax KItem ::= List{Int,""}

endmodule
