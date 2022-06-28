module WITH-CONFIG
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

    syntax Int ::= "total_balance" "(" AccountId ")" [function, functional]
    // -----------------------------------------------------------------------
    rule total_balance(WHO) => 0 [owise]
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
