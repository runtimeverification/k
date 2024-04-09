// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"


module VERIFICATION
  imports TEST

  rule notAFunction => 1 [simplification]
endmodule

module A6-SPEC
  imports VERIFICATION

  claim [s1]:
    <k> run(5) => .K </k> <counter> n => 0 </counter>

endmodule
