requires "with-config.k"

module OWISE-SPEC
    imports WITH-CONFIG

    claim <k> a(AID) => 0 </k>
        <accounts>
            <account>
                <accountID> BID </accountID>
                <freeBalance> 30 </freeBalance>
            </account>
        </accounts>
        requires AID =/=K BID
endmodule
