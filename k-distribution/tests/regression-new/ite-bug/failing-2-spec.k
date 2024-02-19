// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module FAILING-2-SPEC
    imports ITE-BUG
    claim <k> JUMPI 2 bool2Word(_X <Int 0) => .K </k>
          <pc> 0 => 2 </pc>
endmodule
