module FAILING-1-SPEC
    imports ITE-BUG
    claim <k> JUMPI 2 bool2Word(_X <Int 0) => . </k>
          <pc> 0 => 1 </pc>
endmodule
