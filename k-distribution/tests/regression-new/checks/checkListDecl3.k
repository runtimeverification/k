// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module CHECKLISTDECL3-SYNTAX
    syntax Pgm
endmodule

module CHECKLISTDECL3
    imports CHECKLISTDECL3-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax KItem ::= Int "+" List{Int,""}

endmodule
