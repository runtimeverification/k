requires "mini-kevm.k"

module MINI-KEVM-SPEC
    imports MINI-KEVM

    claim [ensures-constraint]:
      <k> a => b ... </k>
      <id> ACCT_ID </id>
      <accounts>
        <account>
          <acctID> ACCT_ID </acctID>
          <storage>
            #hashedLocation("Solidity", 4, .IntList)          |-> STOPPED
            #hashedLocation("Solidity", 1, FROM_ID)           |-> STOPPED
            #hashedLocation("Solidity", 2, FROM_ID CALLER_ID) |-> STOPPED
            _:Map
          </storage>
          <origStorage>
            #hashedLocation("Solidity", 4, .IntList)          |-> STOPPED
            #hashedLocation("Solidity", 1, FROM_ID)           |-> STOPPED
            #hashedLocation("Solidity", 2, FROM_ID CALLER_ID) |-> STOPPED
            _:Map
          </origStorage>
        </account>
        ...
      </accounts>
    requires #rangeUInt(160, ACCT_ID)
     andBool #rangeUInt(160, CALLER_ID)
     andBool #rangeUInt(160, FROM_ID)
     andBool #rangeUInt(256, STOPPED)
     andBool #hashedLocation("Solidity", 4, .IntList)          =/=Int #hashedLocation("Solidity", 1, FROM_ID)
     andBool #hashedLocation("Solidity", 4, .IntList)          =/=Int #hashedLocation("Solidity", 2, FROM_ID CALLER_ID)
     andBool #hashedLocation("Solidity", 2, FROM_ID CALLER_ID) =/=Int #hashedLocation("Solidity", 1, FROM_ID)

endmodule
