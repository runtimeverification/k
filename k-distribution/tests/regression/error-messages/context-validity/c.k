// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module C-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Pgm
endmodule

module C
    imports DOMAINS
    imports C-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
    </T>

syntax KItem ::= foo(K,K)
               | bar(K)

context foo(HOLE => bar(HOLE), HOLE => 0)

endmodule
