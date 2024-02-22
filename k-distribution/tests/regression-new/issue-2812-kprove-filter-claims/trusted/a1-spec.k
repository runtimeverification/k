// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"


module VERIFICATION
  imports TEST

  claim [s1]:
    <k> 1 => 2 </k> // should fail but marked as trusted whould pass

endmodule

module A1-SPEC
  imports VERIFICATION

endmodule
