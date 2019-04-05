module PASSING-SPEC
    imports ITE-BUG
    rule <k> JUMPI 2 bool2Word(X <Int 0) => . </k>
         <pc> 0 => #if (X <Int 0) #then 2 #else 1 #fi </pc>
endmodule
