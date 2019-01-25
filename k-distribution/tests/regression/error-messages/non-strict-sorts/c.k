// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module C-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Pgm
endmodule

module C
    imports DOMAINS
    imports C-SYNTAX

syntax X

//syntax Bag ::= foo(X) [strict]
//syntax BagItem ::= foo(X) [strict]
//syntax CellLabel ::= foo(X) [strict]

//syntax KItem ::= X [strict]

syntax KItem ::= foo(X) [strict(a)]

endmodule
