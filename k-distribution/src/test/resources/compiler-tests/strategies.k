// Copyright (c) 2014-2019 K Team. All Rights Reserved.
requires "domains.k"

module A-STRATEGY
    imports STRATEGY-ABSTRACT
    imports RULE-TAG-SYNTAX
endmodule

module A
    imports A-STRATEGY

    syntax Exp ::= "x" | "y" | "z" | "zz" | "saved" K

    rule x => y                 [tag(xy)]

    rule x => z                 [tag(xz)]

    rule z => zz                [tag(zzz)]

    configuration <t> <k> $PGM:Exp </k> initSCell(Init) </t>
endmodule
