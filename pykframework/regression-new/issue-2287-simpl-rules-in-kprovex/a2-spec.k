// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"


module VERIFICATION
  imports TEST

  rule <k> (X +Int Y) +Int Z => Z +Int (X +Int Y) </k> [simplification, symbolic(X), concrete(Y, Z)]
endmodule

module A2-SPEC
  imports VERIFICATION

  claim [s1]:
    <k> run(5) => .K </k> <counter> n => 0 </counter>

endmodule
