// Copyright (c) 2015 K Team. All Rights Reserved.
require "domains.k"

module B-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Pgm
endmodule

module B
    imports DOMAINS
    imports B-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
        <in stream="stdinn"> .List </in>
    </T>

endmodule
