module FAILING-SPEC
    imports ITE-BUG
    rule <k> JUMPI 2 bool2Word(X <Int 0) => _ </k>
         <pc> 0 => #if (X <Int 0) #then 1258139859758316 #else _ #fi </pc>
endmodule
