// Copyright (c) 2014-2019 K Team. All Rights Reserved.
requires "domains.k"

module A
    syntax Exp ::= "x" | "y"
    configuration <k> $PGM </k>

    rule x => y
endmodule

module B
    syntax Exp ::= "foo" | "bar"
    configuration <b> foo </b>

    rule <b> foo => bar </b>
endmodule

module C
    imports A
    imports B

    configuration <t> initKCell(Init) initBCell </t>

    rule <k> y => foo ...</k> <b> bar => x </b>
endmodule
