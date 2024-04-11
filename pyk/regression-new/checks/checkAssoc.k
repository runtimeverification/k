// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKASSOC-SYNTAX
    imports BOOL
    imports INT

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= Bool | Int

    syntax Bool ::= Bool "bad1"  Int  [left, function]
                  | Int  "bad2"  Bool [right, function]
                  | Bool "bad3"  Int  [non-assoc, function]
                  | Int  "bad4"  Bool [non-assoc, function]
                  | Bool "good1" Int  [right, function]
                  | Int  "good2" Bool [left, function]
                  | Bool "good3" Bool [non-assoc, function]
                  | Pgm  "sub1"  Int  [right, function]
                  | Int  "sub2"  Pgm  [left, function]
                  | Pgm  "sub3"  Pgm  [non-assoc, function]
endmodule

module CHECKASSOC
    imports CHECKASSOC-SYNTAX
endmodule
