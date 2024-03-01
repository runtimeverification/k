requires "domains.md"

module CELL-MAP
    imports INT
    imports MAP
    imports BOOL
    imports SET

    configuration <k> $PGM:KItem </k>
                  <activeAccounts> .Set </activeAccounts>
                  <accounts>
                    <account multiplicity="*" type="Map">
                      <id> 0 </id>
                      <balance> 0 </balance>
                    </account>
                  </accounts>

    syntax KItem ::= #accountNonexistent ( Int ) [symbol(accountNonexistent)]
    rule <k> #accountNonexistent(I) => true ... </k>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool I in ACCTS

    rule <k> #accountNonexistent(I) => B ==Int 0 ... </k>
         <account>
           <id> I </id>
           <balance> B </balance>
         </account>

endmodule
