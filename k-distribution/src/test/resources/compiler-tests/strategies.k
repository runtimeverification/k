// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "domains.md"

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
