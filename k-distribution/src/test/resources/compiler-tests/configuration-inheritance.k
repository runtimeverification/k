// Copyright (c) 2014-2015 K Team. All Rights Reserved.
requires "domains.k"

module A
    syntax Exp ::= "x" | "y"
    configuration <k> $PGM </k>
endmodule

module B
    imports A

    configuration <t> initKCell(Init) </t>

    rule x => y
endmodule
