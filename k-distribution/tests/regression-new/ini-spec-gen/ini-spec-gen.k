// Copyright (c) 2019 K Team. All Rights Reserved.

module INI-SPEC-GEN-SYNTAX
    imports INT
    syntax MyId ::= "x" | "y" | "z" | foo ( Int ) | bar ( Int ) | baz ( Int ) | begin ( Int ) | end ( Int ) | "end" | seq ( Int )
    syntax Alternate ::= "left" | "right"
endmodule

module INI-SPEC-GEN
    imports INI-SPEC-GEN-SYNTAX

    configuration <k> $PGM:MyId </k> <fooC> 0 </fooC> <alt> left </alt>

    rule <k> x => y         ... </k>
    rule <k> x => z         ... </k>
    rule <k> y => x         ... </k>
    rule <k> y => foo ( 7 ) ... </k>

    rule <k> foo(X) => x ... </k> requires X <=Int 8
    rule <k> foo(X) => z ... </k> requires X  >Int 8

    rule <k> bar(X) => baz(X)        ... </k> <fooC> Y </fooC> requires Y <=Int 3
    rule <k> bar(X) => baz(X -Int 1) ... </k> <fooC> Y </fooC> requires Y  >Int 3

    rule <k> baz(X) => bar(X -Int 1) ... </k> requires X  >Int 0
    rule <k> baz(X) => end           ... </k> requires X <=Int 0

    rule <k> begin(X) => end(X) ... </k> <alt> left  </alt>
    rule <k> begin(X) => end(X) ... </k> <alt> right </alt>

    rule <k> end(X) => baz(X) ... </k> requires X <=Int 0
    rule <k> end(X) => end    ... </k> requires X  >Int 0

    rule <k> seq(0) => seq(1) ... </k>
    rule <k> seq(1) => seq(2) ... </k>
    rule <k> seq(2) => seq(3) ... </k>
endmodule

