// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module PASSING-SPEC
    imports ITE-BUG
    claim <k> JUMPI 2 bool2Word(X <Int 0) => .K </k>
          <pc> 0 => #if (X <Int 0) #then 2 #else 1 #fi </pc>
endmodule
