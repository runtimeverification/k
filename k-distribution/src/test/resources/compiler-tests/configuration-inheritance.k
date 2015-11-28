// Copyright (c) 2014-2015 K Team. All Rights Reserved.
requires "domains.k"

module A
    syntax Exp ::= "x" | "y"
    configuration <k> $PGM </k>
endmodule

module B
    syntax Exp ::= "foo"
    configuration <b> foo </b>
endmodule

module C
    imports A
    imports B

    configuration <t> initKCell(Init) initBCell </t>

    rule x => y
endmodule
