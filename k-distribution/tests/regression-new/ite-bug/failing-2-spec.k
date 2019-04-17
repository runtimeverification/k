module FAILING-2-SPEC
    imports ITE-BUG
    rule <k> JUMPI 2 bool2Word(X <Int 0) => . </k>
         <pc> 0 => 2 </pc>
endmodule
