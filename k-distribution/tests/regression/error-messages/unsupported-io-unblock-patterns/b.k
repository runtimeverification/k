// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module B-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Pgm ::= "read"
endmodule

module B
    imports DOMAINS
    imports B-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
        <in stream="stdin"> .List </in>
    </T>

    rule <k> read => V ... </k>
         <in> ListItem(V:Int) => .List </in>

    rule <k> read => V ... </k>
         <in> ListItem(V:Int) ... </in>

    rule <k> read => V ... </k>
         <in> ListItem(V:Int) </in>

    rule <k> read => V ... </k>
         <in> ListItem(V:Int) ListItem(_:Int) => .List  ... </in>

    rule <k> read => V ... </k>
         <in> ListItem(V:Int) ListItem(W:Int) => ListItem(W:Int) ... </in>

    rule <k> read => V ... </k>
         <in> (ListItem(V:Int) => .List) ListItem(_:Int) ... </in>

endmodule
