// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module B-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Pgm
endmodule

module B
    imports DOMAINS
    imports B-SYNTAX

syntax X

//syntax Bag ::= foo(X) [strict]
//syntax BagItem ::= foo(X) [strict]
//syntax CellLabel ::= foo(X) [strict]

syntax KItem ::= X [strict]

//syntax KItem ::= foo(X) [strict(a)]

endmodule
