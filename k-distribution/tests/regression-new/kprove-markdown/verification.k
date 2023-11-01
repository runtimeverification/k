// Copyright (c) K Team. All Rights Reserved.

requires "set-balance.md"

module VERIFICATION
    imports SET-BALANCE

    syntax Action ::= totalBalance ( AccountId )
 // --------------------------------------------
    rule <k> totalBalance(AID) => total_balance(AID) ... </k>
endmodule
