// Copyright (c) 2014-2016 K Team. All Rights Reserved.
requires "domains.k"

module A-STRATEGY
    imports BASIC-STRATEGY
endmodule

module A
    imports A-STRATEGY

    syntax Exp ::= "x" | "y" | "z" | "zz" | "saved" K

    rule x => y                 [tag(xy)]

    rule x => z                 [tag(xz)]

    rule z => zz                [tag(zzz)]

    configuration <t> <k> $PGM:Exp </k> initSCell(Init) </t>
endmodule
