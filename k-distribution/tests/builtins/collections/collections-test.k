// Copyright (c) 2018 K Team. All Rights Reserved.
requires "domains.k"

module COLLECTIONS-TEST-SYNTAX
    imports COLLECTIONS

    syntax Program ::= Set | List
 // -----------------------------

    syntax Set ::= set ( Int ) [function]
 // -------------------------------------
    rule set(0) => .Set
    rule set(1) => SetItem(1)
    rule set(2) => SetItem(1) SetItem(2) SetItem(3) SetItem(4)
    rule set(3) => SetItem(1) SetItem(1) SetItem(3) SetItem(4)
endmodule

module COLLECTIONS-TEST
    imports COLLECTIONS-TEST-SYNTAX

    configuration <k> $PGM:Program </k>
endmodule
