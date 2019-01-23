// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module D-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Pgm
endmodule

module D
    imports DOMAINS
    imports D-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
    </T>

syntax KItem ::= foo(K,K)
               | bar(K)

context foo(HOLE, X => 0)

endmodule
