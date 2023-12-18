// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module WITH-CONFIG-SYNTAX
endmodule

module WITH-CONFIG
    imports WITH-CONFIG-SYNTAX
    imports INT
    imports COLLECTIONS
    imports K-EQUAL

    configuration
        <set-balance>
            <k> $PGM:KItem </k>
            <accounts>
                <account multiplicity="*" type="Map">
                    <accountID> .AccountId:AccountId </accountID>
                    <freeBalance> 0 </freeBalance>
                </account>
            </accounts>
        </set-balance>

    syntax KItem ::= Int

    syntax AccountId ::= ".AccountId" | Int
    // ---------------------------------------

    syntax Int ::= "total_balance" "(" AccountId ")" [function, total]
    // -----------------------------------------------------------------------
    rule total_balance(_WHO) => 0 [owise]
    rule [[ total_balance(WHO) => FREE_BALANCE ]]
        <account>
            <accountID> WHO </accountID>
            <freeBalance> FREE_BALANCE </freeBalance>
        </account>

    // for one-spec
    syntax KItem ::= "aa" "(" AccountId ")"
    rule aa(AID) => total_balance(AID)

    // for owise-spec
    syntax KItem ::= "a" "(" AccountId ")"
    rule a(AID) => total_balance(AID)

endmodule
