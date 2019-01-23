// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module B-SYNTAX

    imports INT-SYNTAX
    imports BOOL-SYNTAX

    syntax KItem ::= foo(Int) | bar(Int)

    rule foo(I) => bar(I) when false [macro]

endmodule

module B

    imports INT
    imports B-SYNTAX

    rule bar(I) => I

endmodule
