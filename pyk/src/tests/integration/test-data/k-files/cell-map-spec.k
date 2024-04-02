requires "cell-map.k"

module CELL-MAP-SPEC
    imports CELL-MAP

    claim [cell-map-no-branch]:
      <k> #accountNonexistent(3) => true ... </k>
      <activeAccounts> SetItem(3) </activeAccounts>
      <account> <id> 3 </id> <balance> 0 </balance> ... </account>

endmodule

