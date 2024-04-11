// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"


module VERIFICATION
  imports TEST
  rule [s1]: notAFunction => 1 [simplification]

  claim <k> run(5) => .K </k> <counter> n => 0 </counter>
endmodule

module A2-SPEC
  imports VERIFICATION
endmodule
